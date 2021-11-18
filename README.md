# Qimaera
Idris libraries for type safe (variational) quantum programming
    
 * [Installing Idris2](#installing)
 * [Compiling Qimaera library](#compiling)
 * [Library overview](#overview)

## <a id="installing"></a> Installing Idris2

These libraries have been tested under Idris2 0.4.0 and 0.5.1.

The latest version of Idris can be found [here](https://www.idris-lang.org/pages/download.html), and all the instructions for installing it can be found [here](https://idris2.readthedocs.io/en/latest/tutorial/starting.html).


## <a id="compiling"></a> Compiling Qimaera library

Type `make package` to build the whole package.

Type `make` to compile the main file and `./run`to run it.

## <a id="overview"></a> Library Overview

### **`Unitary.idr`**

An algebraic representation of unitary quantum circuits.

We first define the `Unitary` data type, which represents the unitary gates. They are only defined as circuits, in terms of gates and wires, and are nor applied to any qubit yet.
The `Unitary` data type is parametrized by the number of wires in the circuit. It has 4 constructors : 
 * `IdGate` : parametrized by a natural number n, it represents a circuit with n wires, without any other gate applied to any of the wires.
 * `H`      : Hadamard gate, takes as argument the index of the wire on which it should be applied (for a circuit of size n, the indices go from 0 to n-1). The second argument, which is implicit (and can be often inferred by the compiler), is a proof obligation that this index is smaller than the size of the circuit.
 * `P`      : Phase gate, its first argument (a Double) being the associated phase. The other arguments serve the same purpose as H.
 * `CNOT`   : Controlled-NOT gate to the control (c argument) and the target (t argument) wires. Here, we add the constraint that the two wires have to be distinct.
As all quantum circuits can be represented as a composition or tensor product of Hadamard, Phase and CNOT gates, we only need these three constructors to build any gate.


Higher level functions to build more complicated circuits are also defined in this file :

 * `compose`    : Makes the sequential composition of unitary gates.
 * `tensor`     : Makes the parallel composition (ie the tensor product) of unitary gates.
 * `apply`      : Apply some unitary gate to another unitary gate.
 * `adjoint`    : Computes the adjoint of a unitary operator.
 * `controlled` : Make the controlled version of unitary gate.

Some examples using these functions can be found in the `Examples.idr` file.

The most common gates (HGate, PGate, CNOTGate, TGate, SGate, ZGate, XGate, RxGate, RyGate, RzGate) are given as unitary gates of size 1 or 2.

Visualize circuits : 

 * `draw`           : Draw a circuit in the terminal.
 * `exportToQiskit` : Export a circuit to Qiskit code for a graphical rendering.

This file also provides some function to compute the number of gates and the depth of a circuit.


### **`QStateT.idr`**

Quantum state transformer for effectful quantum computations (used in the file `QuantumState.idr`).

The type `QStateT initialType finalType returnType` means we are performing a quantum operation from an initial state with type initialType, to a final state with type finalType, and we are returned a value of type returnType.

This was inspired by the indexed state monad in Haskell and adapted to linear types. 


### **`QuantumState.idr`**

Defines the `Qubit` type, the `QuantumState` interface for quantum operations and provides an implementation of this interface for simulations.

The Qubit type is used to identify individual qubits. This type does not carry any quantum state information.

The QuantumState interface is an abstraction over the representation of a quantum state. It is parameterised by the number of qubits it contains. It introduces a few operations on qubits:
 * `newQubits`    : Adds p new qubits to a quantum state.
 * `applyUnitary` : Apply a unitary gate to a set of qubits. The parameters are the linear vector of qubit identifiers for the set of qubits and the unitary operator.
 * `measure`      : Measure a set of qubits. The parameters is the linear vectors of identifiers for the qubits we wish to measure.
 * `run`          : Run a sequence of quantum operations, starting with no qubits and measuring all the qubits at the end.

This interface is then implemented for the type SimulatedState, which simulates them using the linear algebraic representation of qubits and unitary operators. Some examples are given in `Examples.idr`

### **`Examples.idr`**

The file contains simple examples of programs (unitary circuits and quantum operations) to get started with the libraries.

### **`BrokenExamples.idr`**

The file contains common examples of wrong programs that can be detected by Idris compiler.


### **`Lemmas.idr`**

Proofs of all the lemmas used to define all the basic function in `Unitary.idr`. Some of these lemmas are reused in quantum algorithms.

### **`LinearTypes.idr`**

Defines some linear types such as linear vectors, and implements some basic functions with these types.

### **`Matrix.idr`**

Defines all necesary matrix operations for quantum state simulations.

### **`QFT.idr`**

The quantum circuit for the Quantum Fourier Transform. Calling `qft n` returns the QFT for n qubits.

### **`Teleportation.idr`**

Implementation of the quantum teleportation protocol. 
The function `runTeleportation` runs the teleportation protocol where the qubit to be teleported is in state |+>.

### **`VanillaQAOA.idr`**

Implementation of QAOA with vanilla optimisation procedure to solve the MAXCUT problem.
QAOA is an example of variational quantum algorithm that is used to solve optimisation problems.
This code shows how classical and quantum information interact.


### **`Graph.idr`**

Definition of graphs used in `VanillaQAOA.idr` for solving the MAXCUT problem.

### **`VQE.idr`**

Implementation of VQE with vanilla optimisation.
VQE is used find an upper bound for the lowest eigenvalue of a Hamiltonian operator.
It is also a quantum variational algorithm.

### **`RUS.idr`**

Implementation of Repeat until success.

This example illustrates the difference between computing unitary operators and doing effectful quantum operations : here we use measurements to apply a unitary operator to a qubit.

Given an input qubit |q> and a single-qubit unitary operation U, return the state U|q>. The "Repeat Until Success" approach solves this problem in the following way:

 1. Prepare a new qubit in state |0>.
 2. Apply some two-qubit unitary operation U' (depends on U).
 3. Measure the auxiliary qubit.
 4. With (high) probability the result is now U|q> and then stop.
 5. With (low) probability the result is state E|q>, where E is some other unitary operator (depending on U), so we uncompute the error by applying E^dagger and we go back to step 1.

### **`CoinToss.idr`**

A quantum state transformer which realises a fair coin toss in the obvious way: 
 * first create a new qubit in state |0>
 * then apply a hadamard gate to it, thereby preparing state |+>
 * and finally measure the qubit and return this as the result


### **`OptimiseUnitary.idr`**

A small program for a first optimisation of quantum circuits. The main purpose here is to show how unitary gates in Qimaera can be manipulated to be optimised with respect to some criterion.

### **`Main.idr`**

More examples on the different algorithms we implemented.
Uncomment some lines to execute the corresponding programs.


## Getting Started

We recommend starting with...
