import Smt

set_option trace.smt.debug true
set_option trace.smt.translate.expr true
set_option trace.smt.translate.query true

namespace DecEq

theorem extracted {round : Type} [round_dec : DecidableEq round]
  (st_one_a : round → Bool) (st'_one_a : round → Bool)
  (hnext : ∃ r, (∀ (x : round), st'_one_a x = if x = r then true else st_one_a x))
  : True := by
  smt [hnext]
  simp [Smt.Reconstruct.andN']

end DecEq

namespace Uninterpreted
variable {T : Type} [Nonempty T] (le : T → T → Bool)

axiom refl    : ∀ x, le x x
axiom trans   : ∀ x y z, le x y → le y z → le x z
axiom antisym : ∀ x y, le x y → le y x → x = y
axiom total   : ∀ x y, le x y ∨ le y x

example : ∀ x, le x x := by
  smt [refl le]
  simp [Smt.Reconstruct.andN']

end Uninterpreted

section UninterpretedWithClass
class TotalOrder (t : Type) :=
  -- relation: total order
  le (x y : t) : Bool
  -- axioms
  le_refl       (x : t) : le x x
  le_trans  (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total    (x y : t) : le x y ∨ le y x

variable {t : Type} [ne : Nonempty t]
example [tot : TotalOrder t] :
  ∀ (x : t), TotalOrder.le x x := by
  rcases tot with ⟨le, le_refl, le_trans, le_antisymm, le_total⟩
  dsimp only [TotalOrder.le]
  smt [le_refl]
  simp [Smt.Reconstruct.andN']

end UninterpretedWithClass
