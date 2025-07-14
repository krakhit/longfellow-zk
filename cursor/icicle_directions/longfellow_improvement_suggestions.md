# Frontend 

---

## 1. Introduce a High-Level Circuit DSL or API

- Add a domain-specific language (DSL) for circuit definition  similar to Circom, Halo2, or Plonky2.
- Alternatively, provide a higher-level C++ API to make circuit construction more declarative.
  - **Example:** `circuit.add_constraint(a * b == c)` instead of manually building quadratic constraints.

---

## 2. Automatic Constraint System Generation

- Implement automatic constraint generation from high-level operations. (compiler)
- Add constraint optimization passes (e.g., combining multiple constraints, eliminating redundant ones). (compiler)
- Support for different constraint system formats (R1CS, AIR, PLONK, etc.).

---

## 3. Prover-Agnostic Circuit Representation

- Currently the circuit is written to support GKR/Ligero
- Decouple circuit construction from specific proof systems.
- Introduce a universal intermediate representation (IR) for circuits. (like NOIR)
- Provide backend adapters for different provers (Sumcheck, Ligero, PLONK, STARKs, etc.).
- **Example:** Same circuit definition can target multiple proof systems without rewriting.

---

## 4. Add to Standard Library of Circuit Components

- Build a comprehensive library of reusable circuit components:
  - **Cryptographic primitives:** SHA-256, Keccak, ECDSA, EdDSA, Poseidon
  - **Arithmetic operations:** Range checks, comparisons, modular arithmetic
  - **Data structures:** Merkle trees, lookup tables, permutation checks
  - **Protocol-specific components:** Commitment schemes, polynomial operations

---

## 6. Field and Curve Genericity

- Template-based design for arbitrary finite fields and elliptic curves.
- Runtime field/curve selection without recompilation.
- Support for extension fields and pairing-friendly curves.

---

## 7. Performance Optimization Framework

- Automatic parallelization of circuit operations.
- Memory layout optimization for better cache performance.
- SIMD and GPU acceleration where applicable.
- Lazy evaluation and constraint batching.

---

## 8. Icicle C++ Integration: Deep Analysis and Roadmap

### **Overview of Icicle's C++ Architecture**

#### **Core Icicle C++ API Structure:**

- **Runtime Management:** `icicle/runtime.h` - Device management, memory allocation, stream handling
- **Field Operations:** Support for multiple fields (babybear, stark252, m31, koalabear) with templated arithmetic
- **Curve Operations:** Support for curves (bn254, bls12_377, bls12_381, bw6_761, grumpkin) with MSM, point operations
- **Polynomial Operations:** `icicle/polynomials/polynomials.h` - NTT-based polynomial arithmetic, interpolation, evaluation
- **Number Theoretic Transform:** `icicle/ntt.h` - Forward/inverse NTT with domain management
- **Multi-Scalar Multiplication:** `icicle/msm.h` - High-performance MSM for elliptic curve operations
- **Hash Functions:** Keccak, Poseidon, and other cryptographic hash implementations
- **protocols** Sumcheck, FRI

### **Specific Longfellow-to-Icicle Functionality Mapping**

#### **1. Field Arithmetic Replacement**

**Longfellow Current:** Manual field operations in `lib/algebra`

```cpp
// Longfellow style
template<typename Field>
Field add(const Field& a, const Field& b) { return a + b; }
```

**Icicle Replacement:**

```cpp
// Icicle style - hardware accelerated
#include "icicle/curves/params/bn254.h"
using namespace bn254;

scalar_t a = scalar_t::rand_host();
scalar_t b = scalar_t::rand_host();
scalar_t result = a + b;  // GPU/CPU accelerated operations
```

#### **2. Polynomial Operations Enhancement**

**Longfellow Current:** Basic polynomial operations in `lib/algebra/`
**Icicle Enhancement:**

```cpp
#include "icicle/polynomials/polynomials.h"
#include "icicle/ntt.h"

using bn254Poly = Polynomial<scalar_t>;

// High-performance polynomial multiplication using NTT
bn254Poly f = randomize_polynomial(1024);
bn254Poly g = randomize_polynomial(1024);
auto result = f * g;  // Executes on GPU/CPU with optimal performance
```

#### **3. Circuit Constraint Backend Acceleration**

**Current Integration Point:** Replace `lib/circuits/logic/compiler_backend.h` operations

**Icicle Integration:**

```cpp
// Replace Longfellow's constraint compilation with Icicle-accelerated operations
class IcicleConstraintBackend {
    // Use Icicle's MSM for witness computations
    eIcicleError compute_witness_msm(const scalar_t* scalars, const affine_t* points, 
                                     size_t size, projective_t* result) {
        MSMConfig config = default_msm_config();
        return msm(scalars, points, size, config, result);
    }
    
    // Use Icicle's NTT for polynomial constraint evaluation
    eIcicleError evaluate_constraints_ntt(scalar_t* polynomials, size_t size) {
        NTTConfig config = default_ntt_config();
        return ntt(polynomials, size, NTTDir::kForward, config, polynomials);
    }
};
```

#### **4. Hardware Acceleration Integration**

**Device Management Integration:**

```cpp
class LongfellowIcicleRuntime {
public:
    static void initialize() {
        // Load Icicle backends
        ICICLE_CHECK(icicle_load_backend_from_env_or_default());
        
        // Try CUDA, fallback to CPU
        if (icicle_is_device_available("CUDA") == eIcicleError::SUCCESS) {
            Device device = {"CUDA", 0};
            ICICLE_CHECK(icicle_set_device(device));
        }
    }
    
    static void* allocate_device_memory(size_t size) {
        void* ptr;
        ICICLE_CHECK(icicle_malloc(&ptr, size));
        return ptr;
    }
};
```

### **Concrete Integration Roadmap**

#### **Phase 1: Foundation Integration (Weeks 1-4)**

1. **Setup Icicle as Dependency**

   ```cmake
   # CMakeLists.txt addition
   find_package(icicle REQUIRED)
   target_link_libraries(longfellow PRIVATE icicle_field_babybear icicle_device)
   ```

2. **Replace Field Operations**
   - Replace `lib/algebra/fp.h` with Icicle field types
   - Update `lib/algebra/blas.h` to use Icicle vector operations
   - Benchmark performance improvements (expect 10-100x speedup on GPU)

#### **Phase 2: Polynomial System Integration (Weeks 5-8)**

1. **NTT Integration**

   ```cpp
   // Replace FFT operations in lib/algebra/ with Icicle NTT
   class IcicleNTTProvider {
       static void forward_ntt(scalar_t* data, size_t size) {
           ntt_init_domain(scalar_t::omega(log2(size)), default_ntt_init_domain_config());
           ICICLE_CHECK(ntt(data, size, NTTDir::kForward, default_ntt_config(), data));
       }
   };
   ```

2. **Polynomial Operations**
   - Replace polynomial multiplication in sumcheck with Icicle's optimized versions
   - Integrate polynomial interpolation/evaluation for circuit compilation

#### **Phase 3: Prover Backend Integration (Weeks 9-12)**

1. **MSM Integration for Commitments**

   ```cpp
   // Replace manual commitment computations with Icicle MSM
   class IcicleCommitmentScheme {
       projective_t commit(const scalar_t* values, const affine_t* generators, size_t size) {
           projective_t result;
           MSMConfig config = default_msm_config();
           ICICLE_CHECK(msm(values, generators, size, config, &result));
           return result;
       }
   };
   ```

2. **Memory Management Optimization**
   - Use Icicle's async memory operations for better pipeline performance
   - Implement stream-based computation for overlapping CPU/GPU work

#### **Phase 4: Advanced Features (Weeks 13-16)**

1. **Multi-Backend Support**
   - Support both CPU and GPU execution paths
   - Runtime backend selection based on problem size
   - Automatic memory transfer optimization

2. **Curve Agnostic Design**

   ```cpp
   template<typename CurveConfig>
   class IcicleBackedProver {
       using scalar_t = typename CurveConfig::scalar_t;
       using point_t = typename CurveConfig::affine_t;
       
       // Generic prover that works with any Icicle-supported curve
   };
   ```

---