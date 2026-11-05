import Mathlib

namespace MCore.Research.PNP

variable {A B C S : Type}

structure Translation (X Y : Type) (semX : X → S) (semY : Y → S) where
  run : X → Y
  preserves : ∀ x, semY (run x) = semX x

theorem two_path_semantics
    (semA : A → S) (semB : B → S) (semC : C → S)
    (f01 : Translation A B semA semB)
    (f12 : Translation B C semB semC)
    (f02 : Translation A C semA semC)
    (x : A) :
    semC (f12.run (f01.run x)) = semC (f02.run x) := by
  rw [f12.preserves, f01.preserves, f02.preserves]

end MCore.Research.PNP
