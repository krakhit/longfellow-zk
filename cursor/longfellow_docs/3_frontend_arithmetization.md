# Frontend (Arithmetization) in Longfellow ZK

```mermaid
flowchart TD
    subgraph High-Level Input
        A1[Predicate Definition<br/>C++ Code]
        A2[Input Specifications<br/>Public/Private]
        A3[Circuit Builder API<br/>QuadCircuit]
    end
    
    subgraph Circuit Construction
        B1["input() - Create Input Wires"]
        B2["add() - Addition Gates"]
        B3["mul() - Multiplication Gates"]
        B4["assert0() - Constraints"]
        B5["konst() - Constants"]
        B6[DAG Construction<br/>Node Graph]
    end
    
    subgraph Algebraic Optimization
        C1[Constant Propagation<br/>Fold k1 + k2 → k3]
        C2[Common Subexpression Elimination<br/>Reuse x*y computations]
        C3[Dead Code Elimination<br/>Remove unused wires]
        C4[Depth Minimization<br/>Reduce circuit layers]
        C5[Linear Term Optimization<br/>Handle 1*x efficiently]
    end
    
    subgraph Node Management
        D1[Hash-based CSE Table<br/>PdqHash]
        D2[Node Canonicalization<br/>Standardize representation]
        D3[Dependency Tracking<br/>Mark needed nodes]
        D4[Wire ID Assignment<br/>Unique identifiers]
    end
    
    subgraph Layer Scheduling
        E1[Depth Computation<br/>Topological ordering]
        E2[Layer Assignment<br/>Group by depth]
        E3[Copy Wire Generation<br/>Multi-layer spanning]
        E4[Wire Renaming<br/>Layer-local IDs]
        E5[Layer Optimization<br/>Minimize overhead]
    end
    
    subgraph Quad Gate Generation
        F1[Term Collection<br/>Gather quadratic terms]
        F2[Quad Corner Assignment<br/>Gate/Hand variables]
        F3[Coefficient Optimization<br/>Sparse representation]
        F4[Gate Canonicalization<br/>Standard form]
        F5[Layer Quad Assembly<br/>Per-layer gates]
    end
    
    subgraph Circuit Finalization
        G1[Circuit Metadata<br/>Sizes, boundaries]
        G2[Layer Structure<br/>Wire counts, quad gates]
        G3[Input/Output Mapping<br/>Public/private layout]
        G4[Circuit ID Generation<br/>Unique hash]
        G5[Sumcheck Circuit<br/>Final output]
    end
    
    A1 --> B1
    A2 --> B1
    A3 --> B1
    
    B1 --> B6
    B2 --> B6
    B3 --> B6
    B4 --> B6
    B5 --> B6
    
    B6 --> C1
    C1 --> C2
    C2 --> C3
    C3 --> C4
    C4 --> C5
    
    C5 --> D1
    D1 --> D2
    D2 --> D3
    D3 --> D4
    
    D4 --> E1
    E1 --> E2
    E2 --> E3
    E3 --> E4
    E4 --> E5
    
    E5 --> F1
    F1 --> F2
    F2 --> F3
    F3 --> F4
    F4 --> F5
    
    F5 --> G1
    G1 --> G2
    G2 --> G3
    G3 --> G4
    G4 --> G5
    
    classDef input fill:#fff3e0
    classDef construction fill:#e3f2fd
    classDef optimization fill:#f1f8e9
    classDef management fill:#fce4ec
    classDef scheduling fill:#f3e5f5
    classDef quadgen fill:#e0f2f1
    classDef finalization fill:#fff8e1
    
    class A1,A2,A3 input
    class B1,B2,B3,B4,B5,B6 construction
    class C1,C2,C3,C4,C5 optimization
    class D1,D2,D3,D4 management
    class E1,E2,E3,E4,E5 scheduling
    class F1,F2,F3,F4,F5 quadgen
    class G1,G2,G3,G4,G5 finalization
```

## Detailed Arithmetization Process

### High-Level Input
- **Predicate Definition**: User writes C++ code defining the statement to prove
- **Input Specifications**: Designate which inputs are public vs. private
- **Circuit Builder API**: Use QuadCircuit class to construct arithmetic circuits

### Circuit Construction Phase
```cpp
QuadCircuit<Field> qc(field);
size_t x = qc.input();           // Create input wire
size_t y = qc.input();           // Another input wire
size_t z = qc.mul(x, y);         // Multiplication gate
size_t w = qc.add(z, x);         // Addition gate
qc.assert0(w);                   // Constraint: w = 0
```

### Algebraic Optimization
- **Constant Propagation**: Replace `konst(3) + konst(5)` with `konst(8)`
- **CSE**: Reuse computation of `x * y` if it appears multiple times
- **Dead Code Elimination**: Remove wires that don't affect outputs or constraints
- **Depth Minimization**: Reorganize to reduce circuit depth
- **Linear Optimization**: Handle `1 * x` terms efficiently

### Node Management
- **Hash-based CSE**: Use `PdqHash` for fast duplicate detection
- **Canonicalization**: Ensure `mul(x, y)` and `mul(y, x)` are identical
- **Dependency Tracking**: Mark which nodes are actually needed
- **Wire ID Assignment**: Assign unique identifiers to circuit wires

### Layer Scheduling
```cpp
class Scheduler {
  // Convert DAG to layered representation
  std::vector<std::vector<lnode>> order_by_layer();
  
  // Assign wire IDs within each layer
  void assign_wire_ids();
  
  // Generate final circuit structure
  std::unique_ptr<Circuit<Field>> mkcircuit();
};
```

### Quad Gate Generation
Transform arithmetic operations into quad gate representation:
```
Traditional: z = x * y
Quad Gate: ∑ᵢ vᵢ * wₗᵢ * wᵣᵢ where vᵢ=1, wₗᵢ=x, wᵣᵢ=y
```

### Circuit Finalization
Generate final `Circuit<Field>` structure:
```cpp
struct Circuit<Field> {
  size_t nl;                    // Number of layers
  size_t ninputs, npub_in;      // Input counts
  std::vector<Layer<Field>> l;  // Circuit layers
  uint8_t id[32];              // Unique circuit ID
};
```

## Key Data Structures

### Node Representation
```cpp
template <class Field>
struct NodeF {
  std::vector<term> terms;      // Quadratic terms
  NodeInfoF<Field> info;        // Metadata (depth, wire IDs)
};

struct term {
  size_t ki;                    // Constant index
  size_t op0, op1;             // Operand wire IDs
};
```

### Quad Gate Structure
```cpp
template <class Field>
class Quad {
  struct corner {
    quad_corner_t g;            // Gate variable
    quad_corner_t h[2];         // Hand variables (left, right)
    Elt v;                      // Coefficient
  };
  std::vector<corner> c_;       // Quad terms
};
```

### Layer Structure
```cpp
template <class Field>
struct Layer {
  corner_t nw;                  // Number of wires
  size_t logw;                  // Log of wire count
  std::unique_ptr<const Quad<Field>> quad;  // Quadratic gates
};
```

## Optimization Techniques

### Common Subexpression Elimination
- Use cryptographic hash of node structure
- Maintain hash table mapping hash → node ID
- Reuse existing nodes for identical computations

### Constant Propagation
- Fold arithmetic operations on constants at compile time
- Propagate constants through linear operations
- Eliminate multiplications by zero or one

### Dead Code Elimination
- Mark nodes needed for outputs or assertions
- Propagate "needed" marks backward through dependencies
- Remove unmarked nodes from final circuit

### Layer Optimization
- Minimize circuit depth to reduce sumcheck rounds
- Balance layer sizes for efficient processing
- Minimize copy wires between layers

## Example: Simple Circuit Compilation

```cpp
// Input: Prove x² + y² = z
QuadCircuit<Field> qc(field);

// Public input
size_t z = qc.input();
qc.private_input();

// Private inputs
size_t x = qc.input();
size_t y = qc.input();

// Computation
size_t x2 = qc.mul(x, x);      // x²
size_t y2 = qc.mul(y, y);      // y²
size_t sum = qc.add(x2, y2);   // x² + y²
size_t diff = qc.sub(sum, z);  // x² + y² - z
qc.assert0(diff);              // Assert x² + y² - z = 0

// Compile
auto circuit = qc.mkcircuit(1);
```

This produces a layered circuit where:
- Layer 0: Input wires (z, x, y)
- Layer 1: Quadratic operations (x², y²)
- Layer 2: Linear operations (x² + y², x² + y² - z)
- Layer 3: Assertion (x² + y² - z = 0) 