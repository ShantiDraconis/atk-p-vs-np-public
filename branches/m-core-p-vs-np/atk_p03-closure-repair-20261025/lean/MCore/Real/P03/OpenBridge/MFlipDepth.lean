import MCore.Real.P03PerfectFlipDichotomy

namespace MCore.Real.P03.OpenBridge.MFlipDepth

open P03PerfectFlipDichotomy

/--
Terminal construction target for the depth-parity route.
No inhabitant is provided here.  A future physical implementation must prove
its own strict-decrease measure, polynomial runtime, totality and PerfectFlip.
-/
abbrev OpenTarget : Prop :=
  ExistsPerfectFlip

end MCore.Real.P03.OpenBridge.MFlipDepth
