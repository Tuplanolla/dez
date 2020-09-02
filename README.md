# Maniunfold

This is a repository for a research project that aims to

* develop a type-theoretical model of discrete exterior calculus
  (see the related publications),
* formalize the model with the Coq proof assistant
  (see the `fowl` subcomponent),
* extract OCaml code from the proof-relevant parts of the formalization
  (see the `camel` subcomponent),
* link the extracted code with existing numerical solvers
  (see the `truffle` submodule),
* implement a user interface for the resulting system
  (see the `snake` subcomponent) and
* define a protocol for distributing and extending it further
  (see the `flower` subcomponent and the associated
  `feathers`, `leaves`, `fur`, `scales`, `spores` and `hair` subcomponents).

The code in this repository is free software and, as such, licensed under

* the GNU General Public License version 3 or later.

The development of this project

* started around 2018-05-01,
* continues as of 2020-04-01 and
* is expected to reach a usable state by 2022-05-01.

Currently, the authors of this project are

* Jukka Räbinä, who works on the `truffle` submodule
  in the Faculty of Information Technology at the University of Jyväskylä, and
* Sampsa Kiiskinen, who works on all the other parts
  in the Faculty of Information Technology at the University of Jyväskylä.

Over the course of the project,

* Sampsa Kiiskinen has been partially funded by
    * the Jane and Aatos Erkko Foundation grant 170015 and
* Jukka Räbinä has been partially funded by
    * the Academy of Finland grants 259925, 260076 and 295897 and
    * the European Research Council advanced grant 320773.

As is tradition,
the name of this project is a distasteful play on words,
using a taxonomical theme to relate the concepts of

* differentiable manifolds,
  the main objects of study in differential geometry, and
* anamorphisms,
  the generalizations of common recursion schemes from functional programming.

Stay tuned for other equally useful facts about this project.
