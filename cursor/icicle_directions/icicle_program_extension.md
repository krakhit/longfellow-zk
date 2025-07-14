# Extending Icicle Program API for Longfellow ZK Arithmetization

## Motivation

Longfellow ZK uses a constraint-based arithmetization model (e.g., R1CS, PLONK) for zero-knowledge proof circuits. Icicle's program API (`symbol.h`, `program.h`, `returning_value_program.h`) provides a strong foundation for symbolic computation and program representation, but is currently oriented toward imperative compute kernels. Extending Icicle's API to support constraint-based arithmetization will enable high-performance, backend-agnostic ZK circuit construction and execution.

---

## Requirements

1. **Symbolic Variable Management**
   - Support for field elements, wire indices, and ZK-specific metadata.
2. **Constraint Definition**
   - Ability to define and store constraints (e.g., R1CS, PLONK gates).
3. **Expression Building**
   - Support for arithmetic and logical expressions over symbols.
4. **Program/Circuit Encapsulation**
   - Encapsulate variables, constraints, and I/O in a program object.
5. **Witness Assignment**
   - APIs for setting/getting variable assignments (witness values).
6. **Backend Integration**
   - Export circuits/constraints to ZK backends (Longfellow, Icicle, etc.).

---

## Proposed API Extensions

### 1. Extend `Symbol` (`symbol.h`)
- Add field element type information.
- Add wire index and ZK metadata (e.g., public/private, input/output).
- Example:
  ```cpp
  struct ZkSymbol : public Symbol {
      FieldType field_type;
      size_t wire_index;
      bool is_public;
      // ... other ZK metadata
  };
  ```

### 2. Add `Constraint` Abstraction
- New struct/class for constraints:
  ```cpp
  enum class ConstraintType { R1CS, PLONK, ... };
  struct Constraint {
      ConstraintType type;
      std::vector<ZkSymbol> lhs;
      std::vector<ZkSymbol> rhs;
      // ... coefficients, selectors, etc.
  };
  ```

### 3. Extend `Program` (`program.h`)
- Add a constraint list:
  ```cpp
  class Program {
      // ... existing code ...
      std::vector<Constraint> constraints;
      // ...
      void add_constraint(const Constraint& c);
      // ...
  };
  ```
- Add methods for constraint management and serialization.

### 4. Witness Management
- Add APIs for setting/getting variable assignments:
  ```cpp
  class Program {
      // ...
      std::unordered_map<size_t, FieldElement> witness;
      void set_witness(size_t wire, FieldElement value);
      FieldElement get_witness(size_t wire) const;
      // ...
  };
  ```

### 5. Expression Building
- Overload operators for `ZkSymbol` to allow natural arithmetic/logical expression building.
- Optionally, add an `Expression` class to represent symbolic expressions.

### 6. Backend Integration
- Add methods to export the program/constraints to formats required by ZK backends (e.g., Longfellow, Icicle-native, etc.).
- Example:
  ```cpp
  class Program {
      // ...
      void export_r1cs(const std::string& path) const;
      void export_plonk(const std::string& path) const;
      // ...
  };
  ```

---

## Implementation Steps

1. **Design and implement `ZkSymbol` and `Constraint` abstractions.**
2. **Extend `Program` to manage constraints and witness assignments.**
3. **Implement expression building utilities (operator overloads, Expression class).**
4. **Add serialization/export methods for backend integration.**
5. **Write tests and example circuits (e.g., simple R1CS/PLONK circuits).**
6. **Document the new APIs and provide migration guides for Longfellow ZK users.**

---

## Integration Notes

- Ensure backward compatibility with existing Icicle compute kernels.
- Consider performance implications of constraint storage and witness management.
- Provide adapters for existing Longfellow ZK circuits to use the new API.
- Collaborate with Icicle maintainers for upstreaming changes if desired.

---

## References
- [icicle/include/icicle/program/symbol.h](https://github.com/ingonyama-zk/icicle/blob/main/icicle/include/icicle/program/symbol.h)
- [icicle/include/icicle/program/program.h](https://github.com/ingonyama-zk/icicle/blob/main/icicle/include/icicle/program/program.h)
- [icicle/include/icicle/program/returning_value_program.h](https://github.com/ingonyama-zk/icicle/blob/main/icicle/include/icicle/program/returning_value_program.h)
- Longfellow ZK documentation and arithmetization model 