use crate::*;

pub trait IndexLogic<I> {
    type Item;

    #[logic]
    fn index_logic(self, ix: I) -> Self::Item;
}

impl<T> IndexLogic<Int> for Seq<T> {
  type Item = T;


  #[logic]
  #[trusted]
  #[creusot::builtins = "seq.Seq.get"]
  fn index_logic(self, _: Int) -> Self::Item {
    absurd
  }
}

impl<T, S: ShallowModel<ShallowModelTy = Seq<T>>> IndexLogic<Int> for S {
    type Item = T;

    #[logic]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { (@self)[ix] }
    }
}

impl<T, S: ShallowModel<ShallowModelTy = Seq<T>>> IndexLogic<usize> for S {
    type Item = T;

    #[logic]
    fn index_logic(self, ix: usize) -> Self::Item {
        pearlite! { (@self)[@ix] }
    }
}
