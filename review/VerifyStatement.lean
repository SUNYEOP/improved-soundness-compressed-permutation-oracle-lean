import QuantumOracle.Soundness

/-!
# Checking the statement against the full proof

This verification entrypoint intentionally imports the full public theorem.
The separate `review/Statement.lean` imports only the canonical specification.
The public endpoint directly assigns the existing theorem to that specification,
without weakening the claim or adding a premise.

-/

namespace QuantumOracle.StatementReview

/-- The public proved theorem has exactly the canonical proposition. -/
theorem verified : SoundnessStatement := QuantumOracle.soundness

#check QuantumOracle.soundness
#check verified
#print axioms QuantumOracle.soundness
#print axioms verified

end QuantumOracle.StatementReview
