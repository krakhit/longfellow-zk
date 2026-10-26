import RuntimeHahn.LigeroV7SigFS
import examples.Ligero.Longfellow.HahnMaskFSData

/-! The adaptive-FS signature certificate, checked through its exact polynomial. -/
namespace Ligero.Examples.Grid.LongfellowProfiledExtraction.HahnMask

theorem v7SigFS_valid :
    CodingTheory.HahnDelsarte.certificateValid 3187 1626 909 v7SigFS = true :=
  RuntimeHahn.LigeroV7SigFS.certificate_valid

end Ligero.Examples.Grid.LongfellowProfiledExtraction.HahnMask
