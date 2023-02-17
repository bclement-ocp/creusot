use indexmap::IndexSet;
use rustc_ast::Mutability;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{tcx::PlaceTy, Place, PlaceElem},
    ty::{
        DefIdTree, GenericArgKind, InternalSubsts, List, ParamEnv, SubstsRef, Ty, TyCtxt, TyKind,
        TypeSuperVisitable, TypeVisitable, TypeVisitor,
    },
};
use rustc_span::Symbol;
use rustc_type_ir::AliasKind;

use crate::{
    ctx::TranslationCtx,
    translation::{
        fmir::{Block, Body, Branches, Expr, RValue, Statement, Terminator},
        pearlite::{super_visit_term, Pattern, Term, TermKind, TermVisitor},
        traits::{self, TraitImpl},
    },
    util::{self, ItemType, PreSignature},
};

/// Dependencies between items and the resolution logic to find the 'monomorphic' forms accounting
/// for various Creusot hacks like the handling of closures.
///
/// These should be used both to power the cloning system and to order the overall translation of items in Creusot.
///

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub(crate) enum Dependency<'tcx> {
    Type(Ty<'tcx>),
    Item((DefId, SubstsRef<'tcx>)),
}

impl<'tcx> Dependency<'tcx> {
    pub(crate) fn resolve(
        self,
        ctx: &TranslationCtx<'tcx>,
        param_env: ParamEnv<'tcx>,
    ) -> Option<Self> {
        match self {
            Dependency::Type(ty) => resolve_type(ty, ctx.tcx, param_env),
            Dependency::Item((item, substs)) => resolve_item(item, substs, ctx.tcx, param_env),
        }
    }

    pub(crate) fn cloneable_id(self) -> Option<(DefId, SubstsRef<'tcx>)> {
        match self {
            Dependency::Item(i) => Some(i),
            Dependency::Type(t) => match t.kind() {
                TyKind::Adt(def, substs) => Some((def.did(), substs)),
                TyKind::Closure(id, substs) => Some((*id, substs)),
                TyKind::Alias(AliasKind::Projection, aty) => Some((aty.def_id, aty.substs)),
                _ => None,
            },
        }
    }

    pub(crate) fn as_ty(self) -> Option<Ty<'tcx>> {
        match self {
            Dependency::Type(t) => Some(t),
            Dependency::Item(_) => None,
        }
    }
}

fn resolve_type<'tcx>(
    ty: Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
) -> Option<Dependency<'tcx>> {
    let normed = tcx.try_normalize_erasing_regions(param_env, ty);
    match normed {
        Ok(ty) => Some(Dependency::Type(ty)),
        Err(_) => None,
    }
}

fn resolve_item<'tcx>(
    item: DefId,
    substs: SubstsRef<'tcx>,
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
) -> Option<Dependency<'tcx>> {
    let resolved = if tcx.impl_of_method(item).is_some() {
        (item, substs)
    } else {
        traits::resolve_opt(tcx, param_env, item, substs)?
    };
    let resolved = closure_hack(tcx, resolved.0, resolved.1);
    let normed = tcx.try_normalize_erasing_regions(param_env, resolved).unwrap();
    Some(Dependency::Item(normed))
}

fn closure_hack<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    subst: SubstsRef<'tcx>,
) -> (DefId, SubstsRef<'tcx>) {
    if tcx.is_diagnostic_item(Symbol::intern("fn_once_impl_precond"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_once_impl_postcond"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_mut_impl_postcond"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_impl_postcond"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_mut_impl_unnest"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_impl_resolve"), def_id)
    {
        let self_ty = subst.types().nth(1).unwrap();
        if let TyKind::Closure(id, csubst) = self_ty.kind() {
            return (*id, csubst);
        }
    };

    if tcx.is_diagnostic_item(Symbol::intern("creusot_resolve_default"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("creusot_resolve_method"), def_id)
    {
        let self_ty = subst.types().nth(0).unwrap();
        if let TyKind::Closure(id, csubst) = self_ty.kind() {
            return (*id, csubst);
        }
    }

    (def_id, subst)
}

#[derive(Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub(crate) enum DepLevel {
    Body,
    Signature,
}

pub(crate) fn get_deps<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> impl Iterator<Item = (DepLevel, Dependency<'tcx>)> {
    let mut deps = IndexSet::new();
    match util::item_type(ctx.tcx, def_id) {
        ItemType::Type if !util::is_trusted(ctx.tcx, def_id) => {
            let substs = InternalSubsts::identity_for_item(ctx.tcx, def_id);
            let tys = ctx
                .adt_def(def_id)
                .all_fields()
                .map(|f| f.ty(ctx.tcx, substs))
                .flat_map(|fld| fld.walk());

            for arg in tys {
                match arg.unpack() {
                    GenericArgKind::Type(ty) => {
                        ty.deps(ctx.tcx, &mut |dep| {
                            deps.insert((DepLevel::Body, dep));
                        });
                    }
                    GenericArgKind::Lifetime(_) => {}
                    // TODO: slightly wrong if there are const args
                    GenericArgKind::Const(_) => {} // a => panic!("{a:?}"),
                }
            }
        }
        ItemType::Type => {}
        ItemType::Logic | ItemType::Predicate => deps.extend(term_dependencies(ctx, def_id)),
        ItemType::Program => todo!(),
        ItemType::Closure => todo!(),
        ItemType::Trait => todo!(),
        ItemType::Impl => todo!(),
        ItemType::AssocTy => todo!(),
        ItemType::Constant => {
            ctx.type_of(def_id).deps(ctx.tcx, &mut |d| {
                deps.insert((DepLevel::Signature, d));
            });
        }
        ItemType::Unsupported(_) => todo!(),
    }

    deps.into_iter()
}

fn term_dependencies<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> Vec<(DepLevel, Dependency<'tcx>)> {
    let mut deps = IndexSet::new();

    let tcx = ctx.tcx;
    let sig = ctx.sig(def_id);
    sig.deps(tcx, &mut |dep| {
        deps.insert((DepLevel::Signature, dep));
    });

    let tcx = ctx.tcx;
    if let Some(term) = ctx.term(def_id) {
        term.deps(tcx, &mut |dep| {
            deps.insert((DepLevel::Body, dep));
        });
    }

    deps.into_iter().collect()
}

struct TermDep<'tcx, F> {
    f: F,
    tcx: TyCtxt<'tcx>,
}

// Dumb wrapper trait for syntax
trait VisitDeps<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F);
}

impl<'tcx> VisitDeps<'tcx> for TraitImpl<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        self.refinements.iter().for_each(|r| {
            (f)(Dependency::Item(r.trait_));
            r.refn.deps(tcx, f);
        })
    }
}

impl<'tcx> VisitDeps<'tcx> for Term<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        TermDep { f, tcx }.visit_term(self)
    }
}

impl<'tcx> VisitDeps<'tcx> for Ty<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        TermDep { f, tcx }.visit_ty(*self);
    }
}

impl<'tcx> VisitDeps<'tcx> for PreSignature<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        self.contract.terms().for_each(|t| {
            t.deps(tcx, f);
        });

        self.visit_with(&mut TermDep { f, tcx });
    }
}

impl<'tcx> VisitDeps<'tcx> for Expr<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        match self {
            Expr::Place(p) => p.deps(tcx, f),
            Expr::Move(p) => p.deps(tcx, f),
            Expr::Copy(p) => p.deps(tcx, f),
            Expr::BinOp(_, _, l, r) => {
                l.deps(tcx, f);
                r.deps(tcx, f)
            }
            Expr::UnaryOp(_, e) => e.deps(tcx, f),
            Expr::Constructor(id, sub, _, args) => {
                // NOTE: we actually insert a dependency on the type and not hte constructor itself
                // in the interest of coherence we may want ot change that.. idk

                let id = match tcx.def_kind(id) {
                    DefKind::Variant => tcx.parent(*id),
                    _ => *id,
                };
                (f)(Dependency::Item((id, sub)));
                args.iter().for_each(|a| a.deps(tcx, f))
            }
            Expr::Call(id, sub, args) => {
                (f)(Dependency::Item((*id, sub)));
                args.iter().for_each(|a| a.deps(tcx, f))
            }
            Expr::Constant(e) => e.deps(tcx, f),
            Expr::Cast(e, _, _) => e.deps(tcx, f),
            Expr::Tuple(args) => args.iter().for_each(|a| a.deps(tcx, f)),
            Expr::Span(_, e) => e.deps(tcx, f),
            Expr::Len(e) => e.deps(tcx, f),
        }
    }
}

impl<'tcx> VisitDeps<'tcx> for RValue<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        match self {
            RValue::Ghost(t) => t.deps(tcx, f),
            RValue::Borrow(p) => p.deps(tcx, f),
            RValue::Expr(e) => e.deps(tcx, f),
        }
    }
}

impl<'tcx> VisitDeps<'tcx> for Statement<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        match self {
            Statement::Assignment(p, r) => {
                p.deps(tcx, f);
                r.deps(tcx, f)
            }
            Statement::Resolve(id, sub, pl) => {
                (f)(Dependency::Item((*id, sub)));
                pl.deps(tcx, f)
            }
            Statement::Assertion(t) => t.deps(tcx, f),
            Statement::Invariant(_, t) => t.deps(tcx, f),
        }
    }
}

impl<'tcx> VisitDeps<'tcx> for Terminator<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        match self {
            Terminator::Switch(e, b) => {
                e.deps(tcx, f);
                b.deps(tcx, f)
            }
            _ => {}
        }
    }
}

impl<'tcx> VisitDeps<'tcx> for Branches<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, _: TyCtxt<'tcx>, f: &mut F) {
        match self {
            Branches::Constructor(adt, sub, _, _) => (f)(Dependency::Item((adt.did(), sub))),
            _ => {}
        }
    }
}

impl<'tcx> VisitDeps<'tcx> for Block<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        self.stmts.iter().for_each(|s| s.deps(tcx, f));

        self.terminator.deps(tcx, f)
    }
}

impl<'tcx> VisitDeps<'tcx> for Body<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        self.locals.iter().for_each(|(_, _, t)| t.deps(tcx, f));

        self.blocks.values().for_each(|b| b.deps(tcx, f));
    }
}

impl<'tcx> VisitDeps<'tcx> for Place<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, _tcx: TyCtxt<'tcx>, _f: &mut F) {
        panic!()
        // let mut ty = PlaceTy::from_ty(self.ty);
        // for elem in self.projection {
        //     match elem {
        //         PlaceElem::Field(ix, _) => {
        //             match ty.ty.kind() {
        //                 TyKind::Adt(def, subst) => {
        //                     let variant_id = ty.variant_index.unwrap_or_else(|| 0u32.into());
        //                     let variant = &def.variants()[variant_id];
        //                     let field = &variant.fields[ix.as_usize()];

        //                     (f)(Dependency::Item((field.did, subst)))
        //                     // eprintln!("{:?}", field);
        //                 }
        //                 _ => {}
        //             }
        //             // eprintln!("base_ty: {ty:?} field_ty: {fty:?}")
        //         }
        //         _ => {}
        //     };
        //     ty = ty.projection_ty(tcx, elem);
        // }
    }
}

impl<'tcx> VisitDeps<'tcx> for Pattern<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        match self {
            Pattern::Constructor { adt, substs, fields, .. } => {
                // FIXME: Make this `Dependency::Type`
                (f)(Dependency::Item((*adt, substs)));
                fields.iter().for_each(|fld| fld.deps(tcx, f))
            }
            Pattern::Tuple(flds) => flds.iter().for_each(|fld| fld.deps(tcx, f)),
            Pattern::Wildcard => {}
            Pattern::Binder(_) => {}
            Pattern::Boolean(_) => {}
        }
    }
}

impl<'tcx, F: FnMut(Dependency<'tcx>)> TermVisitor<'tcx> for TermDep<'tcx, F> {
    fn visit_term(&mut self, term: &Term<'tcx>) {
        match &term.kind {
            TermKind::Binary { .. } => (self.f)(Dependency::Item((
                self.tcx.get_diagnostic_item(Symbol::intern("creusot_int")).unwrap(),
                List::empty(),
            ))),
            TermKind::Item(id, subst) => (self.f)(Dependency::Item((*id, subst))),
            TermKind::Call { id, subst, fun: _, args: _ } => {
                subst.visit_with(self);
                (self.f)(Dependency::Item((*id, subst)))
            }
            TermKind::Constructor { adt: _, variant: _, fields: _ } => {
                if let TyKind::Adt(_, _) = term.ty.kind() {
                    (self.f)(Dependency::Type(term.ty))
                } else {
                    unreachable!()
                }
            }
            TermKind::Fin { term } => {
                (self.f)(Dependency::Type(term.ty));
            }
            TermKind::Projection { lhs, .. } => match lhs.ty.kind() {
                // TyKind::Closure(def, substs) => (self.f)(Dependency::Item((*def, substs))),
                TyKind::Adt(_, _) => {
                    // let field = &def.variants()[0u32.into()].fields[name.as_usize()];
                    // (self.f)(Dependency::Item((field.did, substs)))
                    (self.f)(Dependency::Type(lhs.ty))
                }
                _ => unreachable!("{:?}", lhs.ty),
            },
            TermKind::Lit(_) => {
                self.visit_ty(term.ty);
            }
            TermKind::Match { arms, .. } => {
                arms.iter().for_each(|(pat, _)| {
                    pat.deps(self.tcx, &mut self.f);
                });
            }
            _ => {}
        };
        super_visit_term(term, self)
    }
}

impl<'tcx, F: FnMut(Dependency<'tcx>)> TypeVisitor<'tcx> for TermDep<'tcx, F> {
    fn visit_ty(&mut self, t: Ty<'tcx>) -> std::ops::ControlFlow<Self::BreakTy> {
        match t.kind() {
            TyKind::Adt(_, sub) => {
                sub.visit_with(self);
                (self.f)(Dependency::Type(t))
            }
            TyKind::Closure(def, _) => {
                if !util::is_logic(self.tcx, *def) {
                    (self.f)(Dependency::Type(t));
                }
            }
            TyKind::Alias(_, pty) => (self.f)(Dependency::Item((pty.def_id, pty.substs))),
            TyKind::Int(_) | TyKind::Uint(_) => (self.f)(Dependency::Type(t)),
            TyKind::Ref(_, _, Mutability::Mut) => (self.f)(Dependency::Type(t)),
            TyKind::RawPtr(_) => (self.f)(Dependency::Type(t)),
            TyKind::Bool => (self.f)(Dependency::Type(t)),
            TyKind::Char => (self.f)(Dependency::Type(t)),
            TyKind::Slice(_) => (self.f)(Dependency::Type(t)),
            TyKind::Array(_, _) => (self.f)(Dependency::Type(t)),
            _ => {}
        };
        t.super_visit_with(self)
    }
}
