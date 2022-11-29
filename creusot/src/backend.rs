use creusot_rustc::{hir::def_id::DefId, resolve::Namespace, span::Symbol};
use rustc_middle::ty::SubstsRef;
use why3::{
    declaration::{self, Decl, Module, Signature},
    exp::Binder,
    QName,
};

use crate::{
    clone_map::CloneMap,
    ctx::TranslationCtx,
    util::{
        self, ident_of, item_name, item_type, pre_sig_of, why3_attrs, AnonymousParamName, ItemType,
        PreSignature,
    },
};

use self::{
    clone_map2::{CloneLevel, Namer, Names, PriorClones},
    logic::translate_logic_or_predicate,
};

pub(crate) mod clone_map2;
pub(crate) mod logic;
pub(crate) mod program;
pub(crate) mod term;
pub(crate) mod ty;

pub(crate) fn to_why3<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    priors: &PriorClones<'_, 'tcx>,
    def_id: DefId,
) -> Vec<Module> {
    match util::item_type(ctx.tcx, def_id) {
        ItemType::Logic | ItemType::Predicate => {
            translate_logic_or_predicate(ctx, priors.get(def_id), def_id)
        }
        ItemType::Program => todo!(),
        ItemType::Closure => todo!(),
        ItemType::Trait => todo!(),
        ItemType::Impl => todo!(),
        ItemType::Type => todo!(),
        ItemType::AssocTy => todo!(),
        ItemType::Constant => todo!(),
        ItemType::Unsupported(_) => todo!(),
    }
}

pub(crate) trait Cloner<'tcx> {
    fn value(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName;

    fn ty(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName;

    fn accessor(
        &mut self,
        def_id: DefId,
        subst: SubstsRef<'tcx>,
        variant: usize,
        ix: usize,
    ) -> QName;

    fn constructor(&mut self, def_id: DefId, subst: SubstsRef<'tcx>, variant: usize) -> QName;

    fn to_clones(&mut self, ctx: &mut TranslationCtx<'tcx>, clone_level: CloneLevel) -> Vec<Decl>;
}

impl<'tcx> Cloner<'tcx> for CloneMap<'tcx> {
    fn value(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
        todo!()
    }

    fn ty(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
        todo!()
    }

    fn accessor(
        &mut self,
        def_id: DefId,
        subst: SubstsRef<'tcx>,
        variant: usize,
        ix: usize,
    ) -> QName {
        todo!()
    }

    fn constructor(&mut self, def_id: DefId, subst: SubstsRef<'tcx>, variant: usize) -> QName {
        todo!()
    }

    fn to_clones(&mut self, ctx: &mut TranslationCtx<'tcx>, clone_level: CloneLevel) -> Vec<Decl> {
        todo!()
    }
}

pub(crate) fn sig_to_why3<'tcx, C: Cloner<'tcx>>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut C,
    pre_sig: PreSignature<'tcx>,
    // FIXME: Get rid of this def id
    // The PreSig should have the name and the id should be replaced by a param env (if by anything at all...)
    def_id: DefId,
) -> Signature {
    let contract = pre_sig.contract.to_exp(ctx, names);

    let name = item_name(ctx.tcx, def_id, Namespace::ValueNS);

    let span = ctx.tcx.def_span(def_id);
    let args: Vec<Binder> = pre_sig
        .inputs
        .into_iter()
        .enumerate()
        .map(|(ix, (id, sp, ty))| {
            let ty = ty::translate_ty(ctx, names, span, ty);
            // I dont like this
            let id = if id.is_empty() {
                format!("{}", AnonymousParamName(ix)).into()
            } else if id == Symbol::intern("result") {
                ctx.crash_and_error(sp, "`result` is not allowed as a parameter name");
            } else {
                ident_of(id)
            };
            Binder::typed(id, ty)
        })
        .collect();

    let mut attrs = why3_attrs(ctx.tcx, def_id);
    if matches!(item_type(ctx.tcx, def_id), ItemType::Program | ItemType::Closure) {
        attrs.push(declaration::Attribute::Attr("cfg:stackify".into()))
    };
    def_id
        .as_local()
        .map(|d| ctx.def_span(d))
        .and_then(|span| ctx.span_attr(span))
        .map(|attr| attrs.push(attr));

    let retty = ty::translate_ty(ctx, names, span, pre_sig.output);
    Signature { name, attrs, retty: Some(retty), args, contract }
}

pub(crate) fn signature_of<'tcx, C: Cloner<'tcx>>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut C,
    def_id: DefId,
) -> Signature {
    debug!("signature_of {def_id:?}");
    let pre_sig = pre_sig_of(ctx, def_id);
    sig_to_why3(ctx, names, pre_sig, def_id)
}
