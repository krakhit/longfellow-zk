# Feature Roadmap: Extending Icicle with Longfellow ZK Capabilities

## 1. Executive Summary

Icicle is a high-performance ZKP compute library with a focus on field, polynomial, and MSM operations, but lacks a high-level, constraint-based circuit/arithmetic abstraction. Longfellow ZK provides a modern, modular frontend for ZKP circuit construction, arithmetization, and optimization, with a clean separation from the backend/prover. Extending Icicle with Longfellow’s features will enable it to support a much broader range of ZKP applications, protocols, and developer workflows.

---

## 2. Key Longfellow Features to Integrate

### A. **Constraint-Based Circuit Abstraction**
- **QuadCircuit**: High-level circuit builder supporting arithmetic and logic gates, assertions, and optimized compilation to sumcheck/Ligero-friendly forms.
- **Constraint System**: Support for R1CS, PLONK, and custom quad gates.
- **Symbolic Variable Management**: Wires, bit vectors, and field elements with metadata (public/private, input/output).

### B. **Frontend Circuit API**
- **Declarative API**: Compose circuits using C++/DSL primitives (add, mul, assert0, assert_eq, etc.).
- **Reusable Gadgets**: Library of cryptographic and arithmetic gadgets (SHA, ECDSA, MAC, Merkle, etc.).
- **Input/Output Handling**: Public/private input separation, vectorized I/O.

### C. **Arithmetization and Optimization**
- **DAG Construction**: Build circuits as directed acyclic graphs for optimization.
- **Compiler Passes**: Constant propagation, common subexpression elimination, dead code elimination, layer scheduling, and quad gate generation.
- **Layered Circuit Model**: Organize gates for efficient sumcheck/Ligero protocols.

### D. **Backend-Agnostic Intermediate Representation**
- **Universal IR**: Decouple circuit definition from proof system; enable targeting multiple backends (Sumcheck, Ligero, PLONK, STARKs).
- **Export/Serialization**: Output circuits in standard formats for interoperability.

### E. **Witness and Proof Management**
- **Witness Assignment**: APIs for setting/getting variable values.
- **Commitment and Padding**: Support for ZK hiding (random padding, Merkle commitments).
- **Proof Generation/Verification**: Integrate with Ligero, Sumcheck, and other protocols.

### F. **Field and Curve Genericity**
- **Template-Based Design**: Support arbitrary fields and curves, including extension fields and pairing-friendly curves.
- **Runtime Selection**: Allow field/curve selection at runtime.

### G. **Performance and Hardware Acceleration**
- **Parallelization**: Automatic parallelization of circuit operations.
- **SIMD/GPU Offload**: Leverage Icicle’s compute kernels for field, polynomial, and MSM operations.
- **Memory Optimization**: Optimize memory layout for cache and GPU.

---

## 3. Icicle Extension Plan

### 1. **API Layer**
- Extend Icicle’s `symbol.h`, `program.h`, and `returning_value_program.h` to support:
  - Symbolic variables with ZK metadata
  - Constraint objects (R1CS, PLONK, quad gates)
  - Circuit encapsulation and serialization
  - Witness management

### 2. **Frontend Circuit Builder**
- Port/implement Longfellow’s `QuadCircuit`, `Logic`, and `CompilerBackend` abstractions.
- Provide a declarative API for circuit construction (C++ or DSL).

### 3. **Constraint System and Optimization**
- Implement compiler passes for circuit optimization.
- Support quad gates and other advanced gate types.

### 4. **Backend Integration**
- Add adapters to export circuits to Icicle’s compute kernels and to external provers.
- Support multiple proof systems via a universal IR.

### 5. **Gadget Library**
- Port Longfellow’s cryptographic and arithmetic gadgets.
- Ensure compatibility with Icicle’s field/curve types.

### 6. **Performance Integration**
- Map high-level operations to Icicle’s GPU-accelerated primitives (field, polynomial, MSM).
- Optimize data movement and memory layout for hardware acceleration.

---

## 4. Feature Mapping Table

| Longfellow Feature                | Icicle Status         | Extension Needed? | Notes/Actions                                 |
|-----------------------------------|----------------------|-------------------|-----------------------------------------------|
| QuadCircuit/Constraint API        | Not present          | Yes               | Implement as new API layer                    |
| R1CS/PLONK/Quad Gate Support      | Not present          | Yes               | Add constraint objects, IR, and serialization |
| Symbolic Variable Management      | Partial (symbol)     | Yes               | Extend symbol abstraction                     |
| Declarative Circuit API           | Not present          | Yes               | Port/implement C++/DSL API                    |
| Circuit Optimization Passes       | Not present          | Yes               | Port compiler passes                          |
| Gadget Library (SHA, ECDSA, etc.) | Not present          | Yes               | Port/implement gadgets                        |
| Field/Curve Genericity            | Partial              | Yes               | Unify with Icicle’s field/curve support       |
| Witness Assignment/Management     | Not present          | Yes               | Add witness APIs                              |
| Commitment/Proof Protocols        | Partial (compute)    | Yes               | Integrate with Ligero, Sumcheck, etc.         |
| Hardware Acceleration             | Strong               | No                | Map new API to existing kernels               |

---

## 5. Product Roadmap Recommendations

### **Phase 1: API and IR Foundation**
- Extend Icicle’s program API for symbolic variables and constraints.
- Implement universal IR for circuits and constraints.

### **Phase 2: Frontend and Optimization**
- Port/implement QuadCircuit, Logic, and compiler passes.
- Build declarative circuit API and gadget library.

### **Phase 3: Backend and Performance**
- Integrate with Icicle’s compute kernels for field/polynomial/MSM.
- Add adapters for multiple proof systems (Ligero, Sumcheck, PLONK, STARKs).

### **Phase 4: Usability and Ecosystem**
- Documentation, examples, and migration guides.
- Interoperability with other ZKP tools and formats.

---

## 6. References

- [Arithmetization in Longfellow (step-by-step, primitives, code links)](arithmetization_longfellow.md)
- [Longfellow ZK: Comprehensive Documentation](longfellow_zk_documentation.md)
- [Icicle Program Extension Plan](icicle_program_extension.md)
- [Longfellow Improvement Suggestions](longfellow_improvement_suggestions.md)
- [Longfellow Frontend Arithmetization](3_frontend_arithmetization.md)
- [Longfellow Backend Prover Workflow](4_backend_prover_workflow.md)

---

**This document is ready to be shared with your software/product team to guide the Icicle extension roadmap.** 