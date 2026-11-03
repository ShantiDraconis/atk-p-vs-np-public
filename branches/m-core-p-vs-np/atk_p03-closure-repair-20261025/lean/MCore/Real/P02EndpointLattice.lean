import MCore.Real.P02RPADualConfirmation

namespace MCore
namespace Real
namespace P02EndpointLattice

open P02RPADualConfirmation

/-- Distinct endpoint positions. -/
inductive EndpointSide
  | open
  | closed
  deriving DecidableEq, Repr

/-- Non-idempotent multiplicity state n·OPEN + m·CLOSED. -/
structure MultiEndpointState where
  openCount : Nat
  closedCount : Nat
  deriving DecidableEq, Repr

def emptyMulti : MultiEndpointState := ⟨0, 0⟩
def openMulti : MultiEndpointState := ⟨1, 0⟩
def closedMulti : MultiEndpointState := ⟨0, 1⟩
def dualMulti : MultiEndpointState := ⟨1, 1⟩

def addMulti (a b : MultiEndpointState) : MultiEndpointState :=
  ⟨a.openCount + b.openCount, a.closedCount + b.closedCount⟩

instance : HAdd MultiEndpointState MultiEndpointState MultiEndpointState :=
  ⟨addMulti⟩

@[simp] theorem open_plus_closed :
    openMulti + closedMulti = dualMulti := rfl

@[simp] theorem open_plus_open :
    openMulti + openMulti = ⟨2, 0⟩ := rfl

@[simp] theorem closed_plus_closed :
    closedMulti + closedMulti = ⟨0, 2⟩ := rfl

@[simp] theorem two_open_one_closed :
    openMulti + openMulti + closedMulti = ⟨2, 1⟩ := rfl

@[simp] theorem one_open_two_closed :
    openMulti + closedMulti + closedMulti = ⟨1, 2⟩ := rfl

@[simp] theorem two_open_two_closed :
    openMulti + openMulti + closedMulti + closedMulti = ⟨2, 2⟩ := rfl

/-- Idempotent quotient: only presence/absence of each side matters. -/
structure CanonicalEndpointState where
  hasOpen : Bool
  hasClosed : Bool
  deriving DecidableEq, Repr

def canonicalize (s : MultiEndpointState) : CanonicalEndpointState :=
  ⟨decide (0 < s.openCount), decide (0 < s.closedCount)⟩

def EMPTY : CanonicalEndpointState := ⟨false, false⟩
def OPEN : CanonicalEndpointState := ⟨true, false⟩
def CLOSED : CanonicalEndpointState := ⟨false, true⟩
def FULL : CanonicalEndpointState := ⟨true, true⟩

def joinCanonical
    (a b : CanonicalEndpointState) : CanonicalEndpointState :=
  ⟨a.hasOpen || b.hasOpen, a.hasClosed || b.hasClosed⟩

instance : HAdd CanonicalEndpointState CanonicalEndpointState CanonicalEndpointState :=
  ⟨joinCanonical⟩

@[simp] theorem canonical_open_idempotent :
    OPEN + OPEN = OPEN := rfl

@[simp] theorem canonical_closed_idempotent :
    CLOSED + CLOSED = CLOSED := rfl

@[simp] theorem canonical_open_closed_full :
    OPEN + CLOSED = FULL := rfl

@[simp] theorem canonical_closed_open_full :
    CLOSED + OPEN = FULL := rfl

theorem canonical_four_cases
    (s : CanonicalEndpointState) :
    s = EMPTY ∨ s = OPEN ∨ s = CLOSED ∨ s = FULL := by
  cases s with
  | mk o c =>
      cases o <;> cases c <;> simp [EMPTY, OPEN, CLOSED, FULL]

/-- Any positive multiplicity on both sides collapses to FULL. -/
theorem canonicalize_both_positive
    (n m : Nat)
    (hn : 0 < n)
    (hm : 0 < m) :
    canonicalize ⟨n, m⟩ = FULL := by
  simp [canonicalize, FULL, hn, hm]

/-- FULL is exactly the maximal dual endpoint presence state. -/
def IsDualMaximal (s : CanonicalEndpointState) : Prop :=
  s.hasOpen = true ∧ s.hasClosed = true

theorem full_is_dual_maximal :
    IsDualMaximal FULL := by
  exact ⟨rfl, rfl⟩

theorem dual_maximal_iff_full
    (s : CanonicalEndpointState) :
    IsDualMaximal s ↔ s = FULL := by
  constructor
  · rintro ⟨ho, hc⟩
    cases s with
    | mk o c =>
        simp [IsDualMaximal, FULL] at ho hc ⊢
        cases o <;> cases c <;> simp_all
  · intro h
    subst s
    exact full_is_dual_maximal

/-- RPA payload carried by the maximal lattice state. -/
abbrev FullPayload : Prop := GLOBAL_EXTERNAL_CERTIFICATE

/-- The maximal canonical state is the lattice view of the global external
certificate; the state label is structural, the payload remains the RPA witness. -/
structure FullCertifiedState where
  state : CanonicalEndpointState
  maximal : state = FULL
  certificate : GLOBAL_EXTERNAL_CERTIFICATE

theorem fullCertified_iff_globalExternal :
    Nonempty FullCertifiedState ↔ GLOBAL_EXTERNAL_CERTIFICATE := by
  constructor
  · rintro ⟨h⟩
    exact h.certificate
  · intro h
    exact ⟨{ state := FULL, maximal := rfl, certificate := h }⟩

/-- Hence FULL/MATH/FINAL_ROOT/GLOBAL_EXTERNAL_CERTIFICATE are the same
inhabitance obligation once the lattice state is maximal. -/
theorem fullCertified_iff_math :
    Nonempty FullCertifiedState ↔ MATH := by
  rw [fullCertified_iff_globalExternal]

#print axioms MCore.Real.P02EndpointLattice.canonical_four_cases
#print axioms MCore.Real.P02EndpointLattice.canonicalize_both_positive
#print axioms MCore.Real.P02EndpointLattice.dual_maximal_iff_full
#print axioms MCore.Real.P02EndpointLattice.fullCertified_iff_globalExternal
#print axioms MCore.Real.P02EndpointLattice.fullCertified_iff_math

end P02EndpointLattice
end Real
end MCore
