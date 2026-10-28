namespace MCore
inductive BoundaryPhase where | regular | preBoundary | boundary | crossing | postBoundary deriving DecidableEq, Repr
inductive BoundaryResult where | uniqueExtension | pathDependent | blowup | oscillatory | removable | nonremovable | discreteJump | noNaturalLimit | open deriving DecidableEq, Repr
end MCore
