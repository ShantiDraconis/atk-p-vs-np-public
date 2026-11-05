import MCore.Research.PatternCalculator

namespace MCore
namespace Research
namespace MetaFormalizerAcceptanceFixture

/-- Synthetic producer used only to prove the promotion/linker path is non-vacuous. -/
structure FixtureCertificate where
  payload : Nat
  payload_zero : payload = 0

def fixture : FixtureCertificate :=
  { payload := 0, payload_zero := rfl }

theorem fixture_inhabited : Nonempty FixtureCertificate :=
  ⟨fixture⟩

#print axioms MCore.Research.MetaFormalizerAcceptanceFixture.fixture
#print axioms MCore.Research.MetaFormalizerAcceptanceFixture.fixture_inhabited

end MetaFormalizerAcceptanceFixture
end Research
end MCore
