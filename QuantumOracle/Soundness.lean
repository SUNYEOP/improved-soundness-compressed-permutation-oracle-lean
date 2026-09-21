import QuantumOracle.Statement.Soundness
import QuantumOracle.Proof.ImprovedSoundness

/-!
# Public improved soundness theorem

The complete specification lives in `QuantumOracle.Statement.Soundness`.
This endpoint connects it to the full proof. Import the statement module for
semantic review; import this module to use the proved theorem.

The direct assignment below makes Lean check that the existing theorem's full
type is definitionally equal to the canonical specification. No assumption is
added, and no conclusion is discarded.
-/

namespace QuantumOracle

/-- The manuscript's improved soundness theorem, proved for exactly the canonical
`SoundnessStatement`. Its parameter and conclusion documentation is attached to
that definition, which can be read and imported without the main proof. -/
theorem soundness : SoundnessStatement := @ImprovedSoundness.soundness

end QuantumOracle
