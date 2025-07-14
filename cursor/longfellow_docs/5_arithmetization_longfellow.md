# Arithmetization in Longfellow

This document explains how arithmetization is handled in the Longfellow library, with step-by-step instructions for writing circuits and a comprehensive list of supported primitives. It is intended for developers seeking to understand, extend, or design a DSL for Longfellow.

---

## 1. Overview:

Longfellow uses a C++-based approach, where circuits are written as C++ code using a set of provided primitives and logic/arithmetic gates. These are compiled into a custom constraint system (quad gates) suitable for sumcheck, Ligero, and GKR protocols.

---

## 1. How to Write Circuits in Longfellow

### Step 1: Choose Field and Backend

- Select the finite field (e.g., GF(2^128), Fp256) and the backend (usually `CompilerBackend`).
- Example:

  ```cpp
  using Field = GF2_128<>;
  QuadCircuit<Field> Q(F);
  const CompilerBackend cbk(&Q);
  const LogicCircuit LC(&cbk, F);
  ```

  - See [`Logic` (logic.h#L37)](../lib/circuits/logic/logic.h#L37), [`CompilerBackend` (compiler_backend.h#L26)](../lib/circuits/logic/compiler_backend.h#L26), [`QuadCircuit` (compiler.h#L49)](../lib/circuits/compiler/compiler.h#L49)

### Step 2: Define Inputs

- Use `Q.input()` for each input wire.
- For bit vectors, use `Logic::vinput<N>()`.
- Example:

  ```cpp
  BitW a = BitW(Q.input(), F);
  auto bits = LC.vinput<8>();
  ```

- See [`QuadCircuit::input()` (compiler.h#L218)](../lib/circuits/compiler/compiler.h#L218), [`Logic::vinput` (logic.h#L969)](../lib/circuits/logic/logic.h#L969)

### Step 3: Build the Circuit Using Primitives

- Use arithmetic and logic gates (see next section) to compose your circuit.
- Example:

  ```cpp
  auto sum = LC.add(&a, b);
  auto and_result = LC.land(&a, b);
  auto xor_result = LC.lxor(&a, b);
  ```

  - See [`Logic` arithmetic/boolean methods (logic.h#L37)](../lib/circuits/logic/logic.h#L37)

### Step 4: Add Constraints

- Use assertion primitives to enforce constraints:
  - `assert0(wire)` (wire == 0)
  - `assert_eq(a, b)` (a == b)
  - `assert_is_bit(wire)` (wire in {0,1})
- Example:

  ```cpp
  LC.assert0(sum);
  LC.assert_eq(&a, b);
  LC.assert_is_bit(bit_wire);
  ```

  - See [`Logic` assertion methods (logic.h#L37)](../lib/circuits/logic/logic.h#L37), [`QuadCircuit::assert0` (compiler.h#L175)](../lib/circuits/compiler/compiler.h#L175)

### Step 5: Define Outputs

- Use `Q.output(wire, index)` to mark outputs.
- Example:
  
  ```cpp
  Q.output(LC.eval(result), 0);
  ```

- See [`QuadCircuit::output()` (compiler.h#L240)](../lib/circuits/compiler/compiler.h#L240), [`Logic::output()` (logic.h#L973)](../lib/circuits/logic/logic.h#L973)

### Step 6: Compile the Circuit

- Call `Q.mkcircuit(nc)` to compile and optimize the circuit.
- Example:

  ```cpp
  auto circuit = Q.mkcircuit(1);
  ```

  - See [`QuadCircuit::mkcircuit()` (compiler.h#L247)](../lib/circuits/compiler/compiler.h#L247)

---

## 3. Supported Primitives in Longfellow

### Arithmetic Primitives

- [`addf(a, b)`, `mulf(a, b)`, `negf(a)`, `invertf(a)` — Field operations (logic.h#L37)](../lib/circuits/logic/logic.h#L37)
- [`add`, `sub`, `mul`, `konst` — Wire operations (logic.h#L37)](../lib/circuits/logic/logic.h#L37)

### Boolean Logic Primitives

- [`lnot(x)` — NOT (logic.h#L37)](../lib/circuits/logic/logic.h#L37)
- [`land(a, b)` — AND (logic.h#L37)](../lib/circuits/logic/logic.h#L37)
- [`lor(a, b)` — OR (logic.h#L37)](../lib/circuits/logic/logic.h#L37)
- [`lxor(a, b)` — XOR (logic.h#L37)](../lib/circuits/logic/logic.h#L37)
- [`limplies(a, b)` — IMPLIES (logic.h#L37)](../lib/circuits/logic/logic.h#L37)
- [`mux(control, iftrue, iffalse)` — Multiplexer (logic.h#L37)](../lib/circuits/logic/logic.h#L37)

### Bit and Vector Primitives

- [`BitW` — Bit wire (logic.h#L37)](../lib/circuits/logic/logic.h#L37)
- [`bitvec<N>` — Bit vector (logic.h#L37)](../lib/circuits/logic/logic.h#L37)
- [`vinput<N>()`, `voutput<N>()` — Vector input/output (logic.h#L969, logic.h#L987)](../lib/circuits/logic/logic.h#L969)

### Assertion Primitives

- [`assert0(wire)` — Assert wire is zero (logic.h#L37, compiler.h#L175)](../lib/circuits/logic/logic.h#L37)
- [`assert1(wire)` — Assert wire is one (logic.h#L37)](../lib/circuits/logic/logic.h#L37)
- [`assert_eq(a, b)` — Assert equality (logic.h#L37)](../lib/circuits/logic/logic.h#L37)
- [`assert_is_bit(wire)` — Assert wire is a bit (logic.h#L37)](../lib/circuits/logic/logic.h#L37)
- [`assert_implies(a, b)` — Assert implication (logic.h#L37)](../lib/circuits/logic/logic.h#L37)

### Specialized Primitives

- Adder circuits: [`BitAdderAux` (bit_adder.h#L36, bit_adder.h#L83)](../lib/circuits/logic/bit_adder.h#L36)
- Multiplier: [`Logic::multiplier` (logic.h#L37)](../lib/circuits/logic/logic.h#L37)
- SHA/Hash-specific: [`lCh`, `lMaj` (logic.h#L37)](../lib/circuits/logic/logic.h#L37)
- Packing/unpacking bits to field elements: [`BitAdderAux::as_field_element` (bit_adder.h#L53)](../lib/circuits/logic/bit_adder.h#L53)
- CBOR plucker: [`CborPlucker` (cbor_pluck.h#L35)](../lib/circuits/cbor_parser/cbor_pluck.h#L35)

### Backend and Compilation Primitives

- [`CompilerBackend` (compiler_backend.h#L26)](../lib/circuits/logic/compiler_backend.h#L26)
- [`EvaluationBackend` (evaluation_backend.h#L22)](../lib/circuits/logic/evaluation_backend.h#L22)
- [`QuadCircuit` (compiler.h#L49)](../lib/circuits/compiler/compiler.h#L49)

### Input/Output Primitives

- [`QuadCircuit::input()` (compiler.h#L218)](../lib/circuits/compiler/compiler.h#L218)
- [`Logic::vinput()` (logic.h#L969)](../lib/circuits/logic/logic.h#L969)
- [`QuadCircuit::output()` (compiler.h#L240)](../lib/circuits/compiler/compiler.h#L240)
- [`Logic::output()` (logic.h#L973)](../lib/circuits/logic/logic.h#L973)

---

## 4. Example: Minimal Circuit

```cpp
using Field = GF2_128<>;
QuadCircuit<Field> Q(F);
const CompilerBackend cbk(&Q);
const LogicCircuit LC(&cbk, F);

// Inputs
auto a = BitW(Q.input(), F);
auto b = BitW(Q.input(), F);

// Circuit logic
auto sum = LC.lxor(&a, b);
LC.assert_is_bit(sum);

// Output
Q.output(LC.eval(sum), 0);

// Compile
auto circuit = Q.mkcircuit(1);
```

---

## 5. Notes for DSL Design

- All primitives above should be exposed in the DSL.
- Automatic constraint generation and variable management would greatly improve usability.
- Consider supporting both arithmetic and boolean logic natively.
- Abstract away backend/proof system details for prover-agnostic circuits.

---

## 6. References

- [`Logic` (logic.h#L37)](../lib/circuits/logic/logic.h#L37)
- [`BitAdderAux` (bit_adder.h#L36, bit_adder.h#L83)](../lib/circuits/logic/bit_adder.h#L36)
- [`CompilerBackend` (compiler_backend.h#L26)](../lib/circuits/logic/compiler_backend.h#L26)
- [`EvaluationBackend` (evaluation_backend.h#L22)](../lib/circuits/logic/evaluation_backend.h#L22)
- [`QuadCircuit` (compiler.h#L49)](../lib/circuits/compiler/compiler.h#L49)
- [`CborPlucker` (cbor_pluck.h#L35)](../lib/circuits/cbor_parser/cbor_pluck.h#L35)
- See example circuits in [`ecdsa/verify_circuit.h`](../lib/circuits/ecdsa/verify_circuit.h), [`jwt/jwt.h`](../lib/circuits/jwt/jwt.h), [`mdoc/mdoc_signature.h`](../lib/circuits/mdoc/mdoc_signature.h).