use indexmap::IndexMap;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::TyCtxt;
use why3::declaration::Module;

use crate::{
    backend::program::{translate_closure, translate_function},
    clone_map::CloneSummary,
    ctx::{ItemType, TranslatedItem, TranslationCtx},
    translation::{interface::interface_for, ty::translate_tydecl, traits::translate_assoc_ty},
    util::{self, item_type},
};

pub(crate) mod dependency;
pub(crate) mod logic;
pub(crate) mod program;
pub(crate) mod term;
pub(crate) mod traits;

pub(crate) struct Why3Backend<'tcx> {
    functions: IndexMap<DefId, TranslatedItem>,
    dependencies: IndexMap<DefId, CloneSummary<'tcx>>,
    pub(crate) ctx: TranslationCtx<'tcx>,
}

impl<'tcx> Why3Backend<'tcx> {
    pub(crate) fn translate(&mut self, def_id: DefId) {
        if self.functions.contains_key(&def_id) || self.ctx.safe_cycle(def_id) {
            return;
        }
        debug!("translating {:?}", def_id);

        // eprintln!("{:?}", self.param_env(def_id));

        match item_type(self.ctx.tcx, def_id) {
            ItemType::Trait => {
                self.ctx.start(def_id);
                let tr = self.ctx.translate_trait(def_id);
                self.dependencies.insert(def_id, CloneSummary::new());
                self.functions.insert(def_id, tr);
                self.ctx.finish(def_id);
            }
            ItemType::Impl => {
                if self.ctx.tcx.impl_trait_ref(def_id).is_some() {
                    self.ctx.start(def_id);
                    let impl_ = traits::lower_impl(self, def_id);

                    self.dependencies.insert(def_id, CloneSummary::new());
                    self.functions.insert(def_id, TranslatedItem::Impl { modl: impl_ });
                    self.ctx.finish(def_id);
                }
            }
            ItemType::Logic | ItemType::Predicate | ItemType::Program | ItemType::Closure => {
                self.ctx.start(def_id);
                self.translate_function(def_id);
                self.ctx.finish(def_id);
            }
            ItemType::AssocTy => {
                self.ctx.start(def_id);
                let (modl, dependencies) = translate_assoc_ty(self, def_id);
                self.ctx.finish(def_id);
                self.dependencies.insert(def_id, dependencies);
                self.functions.insert(def_id, TranslatedItem::AssocTy { modl });
            }
            ItemType::Constant => {
                self.ctx.start(def_id);
                let (constant, dependencies) = self.translate_constant(def_id);
                self.ctx.finish(def_id);
                self.dependencies.insert(def_id, dependencies);
                self.functions.insert(def_id, constant);
            }
            ItemType::Type => {
                translate_tydecl(self, def_id);
            }
            ItemType::Unsupported(dk) => self.ctx.crash_and_error(
                self.ctx.tcx.def_span(def_id),
                &format!("unsupported definition kind {:?} {:?}", def_id, dk),
            ),
        }
    }

    // Generic entry point for function translation
    fn translate_function(&mut self, def_id: DefId) {
        assert!(matches!(
            self.ctx.tcx.def_kind(def_id),
            DefKind::Fn | DefKind::Closure | DefKind::AssocFn
        ));

        if !crate::util::should_translate(self.ctx.tcx, def_id)
            || util::is_spec(self.ctx.tcx, def_id)
        {
            debug!("Skipping {:?}", def_id);
            return;
        }

        let (interface, deps) = interface_for(self, def_id);

        let translated = match util::item_type(self.ctx.tcx, def_id) {
            ItemType::Logic | ItemType::Predicate => {
                debug!("translating {:?} as logical", def_id);
                let (stub, modl, proof_modl, has_axioms, deps) =
                    crate::backend::logic::translate_logic_or_predicate(self, def_id);
                self.dependencies.insert(def_id, deps);
                TranslatedItem::Logic { stub, interface, modl, proof_modl, has_axioms }
            }
            ItemType::Closure => {
                let (ty_modl, modl) = translate_closure(self, def_id);
                self.dependencies.insert(def_id, deps);

                TranslatedItem::Closure { interface: vec![ty_modl, interface], modl }
            }
            ItemType::Program => {
                debug!("translating {def_id:?} as program");

                self.dependencies.insert(def_id, deps);
                let modl = translate_function(self, def_id);
                TranslatedItem::Program { interface, modl }
            }
            _ => unreachable!(),
        };

        self.functions.insert(def_id, translated);
    }

    pub(crate) fn dependencies(&self, def_id: DefId) -> Option<&CloneSummary<'tcx>> {
        self.dependencies.get(&def_id)
    }

    pub(crate) fn add_type(&mut self, def_id: DefId, modl: Vec<Module>) {
        let repr = self.ctx.representative_type(def_id);
        self.functions.insert(repr, TranslatedItem::Type { modl, accessors: Default::default() });
    }

    pub(crate) fn item(&self, def_id: DefId) -> Option<&TranslatedItem> {
        let def_id = self.ctx.representative_type(def_id);
        self.functions.get(&def_id)
    }

    pub(crate) fn modules(self) -> impl Iterator<Item = (DefId, TranslatedItem)> + 'tcx {
        self.functions.into_iter()
    }
}
use std::{collections::HashMap, ops::Deref};


impl<'tcx> Deref for Why3Backend<'tcx> {
    type Target = TyCtxt<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.ctx.tcx
    }
}