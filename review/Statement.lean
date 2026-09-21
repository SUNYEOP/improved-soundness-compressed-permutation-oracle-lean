import QuantumOracle.Statement.Soundness

/-!
# Statement review entrypoint

The proposition and model definitions are imported from their canonical source.
This file does not import the numerical soundness proof. Read
`QuantumOracle/Statement/Soundness.lean` for every parameter, assumption, and
conclusion; follow its model imports or the generated review excerpts for the
definitions. `review/VerifyStatement.lean` separately checks the proved endpoint.

-/

namespace QuantumOracle.StatementReview

/-- Compatibility name for the canonical complete proposition. There is only one
source definition of the assumptions and conclusions. -/
abbrev Statement : Prop := SoundnessStatement

#check SoundnessStatement
#print SoundnessStatement

end QuantumOracle.StatementReview
