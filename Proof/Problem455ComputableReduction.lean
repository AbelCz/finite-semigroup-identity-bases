import Problem455ComputableWriter
import Problem455PayloadBridge
import Problem455TableDecision

namespace P455ComputableReduction

/-- The previously isolated operational assumption follows from the
    standard computability of the first-order machine-to-catalogue map. -/
theorem presentation (code : Computable P455PayloadBridge.selfPayload) :
    P455TableDecision.PresentationWriterExists := by
  obtain ⟨g,r,W,A,run⟩ := P455ComputableWriter.realizes
    (P455PayloadBridge.selfOutput_computable code)
  exact ⟨g,r,W,A,A,P455PackedOutput.delivers_presentation W A A run⟩

theorem reduction (code : Computable P455PayloadBridge.selfPayload) :
    ¬ P455TableDecision.PureDeciderExists :=
  P455TableDecision.no_table_algorithm_of_presentation_writer (presentation code)

end P455ComputableReduction
