# 📘 OpenMath Theorem Registry for DeepMind Formal Conjectures

This repository contains a curated collection of formalized theorems and open conjectures originally from the **DeepMind Formal Conjectures** project, adapted for use in the **OpenMath/Shentu ecosystem**. It includes Lean 4 formalizations of classical problems such as Erdos Problems and others, organized for exploration, collaboration, and publishing on the OpenMath platform.

---

## 🧠 Overview

We aim to provide a bridge between existing formal mathematics work from the DeepMind Formal Conjectures repo and the OpenMath theorem registry. Entries here include:

* Formalized **definitions**
* **Open problem statements** with placeholders (`sorry`)
* **Solved variants** with proofs
* Categorization via namespaces and metadata

All formalizations are written in **Lean 4**, use **Lake** as the project manager, and depend on **mathlib**.

This project is licensed under the **Apache License 2.0** with attribution to the original authors, and includes modifications from OpenMath contributors.

---

## 🚀 Key Features

* **Modular structure**: each problem or variant lives in its own Lean file
* **Clear distinction** between open and solved results
* **Adapted from DeepMind Formal Conjectures** using consistent definitions
* **Compatible with mathlib** for broader interoperability
* **Ready for extension and collaboration**

---

## 🗂 Repository Structure

```
📦 FormalConjectures
├── 📁 ErdosProblems              
├── 📁 GreensOpenProblems         
├── 📁 OEIS                       
├── 📁 Millennium                  
├── 📁 Other                     
├── lakefile.lean               
├── README.md                   
└── LICENSE                     
```

---

## 🛠 Prerequisites

Before building this repository, you need the following:

### 📌 Required tools

* **elan** — Lean version manager
  Install from [https://leanprover.github.io/elan](https://leanprover.github.io/elan)
* **Lean 4**
  Managed by elan
* **Lake** — Lean project build tool
  Included via Lean tooling

### 📌 Recommended (optional)

* **Visual Studio Code**
  With the Lean 4 extension enabled — great for editing, jump-to-definition, interactive goals, and more.

---

## 📦 Installation & Build

Once you have the prerequisites, follow these steps:

1. **Get external dependencies and cached executables**

   ```sh
   lake exe cache get
   ```

2. **Build the project**

   ```sh
   lake build
   ```

After this, you should be able to open Lean files and inspect them interactively in your editor.

## 📣 Contribution Guidelines

We welcome contributions:

* Add new formalized problems
* Improve or complete proofs
* Add metadata, tags, or links to published work
* Organize problems into clearer categories

Before submitting:

* Keep proper licensing information intact
* Follow Lean 4 and Lake idioms
* Reference original sources when applicable


## 📜 License

This repository and all formalizations are licensed under the **Apache License, Version 2.0**.
Original parts from DeepMind Formal Conjectures carry their own headers, which are preserved.
Modifications are clearly labeled per file.

See the full LICENSE file for details.

---

## 🙌 Acknowledgments

* DeepMind Formal Conjectures Contributors
* Lean community maintainers (Lean 4, Lake, mathlib)
* OpenMath & Shentu community for collaboration
