import LfzkV1.FlatV7Headline
import LfzkV1.FlatV7Hash2Headline
import LfzkV1.FlatV7Hash3Headline
import LfzkV1.FlatV7Hash4Headline
import Lean.Util.CollectAxioms

/-!
# All four v7 hash geometries at 116-bit FS extraction and soundness

This default target checks the concrete zero-query coupling and the
positive-query deployed compiler for each registered v7 hash circuit.
It can also be built directly with `lake build LfzkV1.FlatV7All`.
-/

open Lean Elab Command
run_cmd do
  for endpoint in #[
      ``LfzkV1.CompiledZk.FlatV7Headline.v7Hash1_deployed_fs_extraction_116_circuit,
      ``LfzkV1.CompiledZk.FlatV7Headline.v7Hash1_deployed_fs_false_statement_116,
      ``LfzkV1.CompiledZk.FlatV7Hash2Headline.v7Hash2_deployed_fs_extraction_116_circuit,
      ``LfzkV1.CompiledZk.FlatV7Hash2Headline.v7Hash2_deployed_fs_false_statement_116,
      ``LfzkV1.CompiledZk.FlatV7Hash3Headline.v7Hash3_deployed_fs_extraction_116_circuit,
      ``LfzkV1.CompiledZk.FlatV7Hash3Headline.v7Hash3_deployed_fs_false_statement_116,
      ``LfzkV1.CompiledZk.FlatV7Hash4Headline.v7Hash4_deployed_fs_extraction_116_circuit,
      ``LfzkV1.CompiledZk.FlatV7Hash4Headline.v7Hash4_deployed_fs_false_statement_116] do
    for ax in ← collectAxioms endpoint do
      let name := ax.toString
      let nativeRowFact := ax == ``Lean.ofReduceBool ||
        ((name.startsWith "LfzkV1." || name.startsWith "_private.LfzkV1." ||
          name.startsWith "Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized.") &&
          name.contains "._native.native_decide.ax_")
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax || nativeRowFact do
        throwError "Unexpected axiom in V1 116-bit endpoint {endpoint}: {ax}"
