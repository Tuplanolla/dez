#ifdef CLUSTER
#define SUBGRAPH(x) cluster_##x
#else
#define SUBGRAPH(x) uncluster_##x
#endif

digraph habitat {
  /* subgraph SUBGRAPH(fowl) {
    label = "Component\nFowl"
  } */

  subgraph SUBGRAPH(bird) {
    label = "Component\nBird"

    node [shape = box]

    bird [label = "Coq Source\nfor Formal Specification"]
  }

  /* subgraph SUBGRAPH(feathers) {
    label = "Component\nFeathers"
  } */

  /* subgraph SUBGRAPH(flower) {
    label = "Component\nFlower"
  } */

  subgraph SUBGRAPH(plant) {
    label = "Component\nPlant"

    node [shape = box]

    plant [label = "Thrift IDL Source\nfor Message Specification"]
  }

  /* subgraph SUBGRAPH(leaves) {
    label = "Component\nLeaves"
  } */

  subgraph SUBGRAPH(camel) {
    label = "Component\nCamel"

    node [shape = box]

    camel [label = "OCaml Source\nfor Common Tasks"]

    node [shape = oval]

    camel_from_camel [label = "Utility Library\nfor Common Tasks"]
  }

  subgraph SUBGRAPH(ungulate) {
    label = "Component\nUngulate"

    node [shape = box]

    ungulate [label = "OCaml Source\nfor Symbolic Manipulation"]
    ungulate_from_bird [label = "OCaml Source\nfor Formal Verification"]

    node [shape = oval]

    ungulate_from_ungulate [label = "Server Library\nfor Verified Symbolic Manipulation"]
  }

  subgraph SUBGRAPH(fur) {
    label = "Component\nFur"

    node [shape = box]

    fur [label = "OCaml Source\nfor Message Interpretation"]
    fur_from_plant [label = "OCaml Source\nfor Message Transmission"]

    node [shape = oval]

    fur_from_fur [label = "Server Proxy\nfor Verified Symbolic Manipulation"]
  }

  subgraph SUBGRAPH(snake) {
    label = "Component\nSnake"

    node [shape = box]

    snake [label = "Python Source\nfor Common Tasks"]

    node [shape = oval]

    snake_from_snake [label = "Utility Library\nfor Common Tasks"]
  }

  subgraph SUBGRAPH(reptile) {
    label = "Component\nReptile"

    node [shape = box]

    reptile [label = "Python Source\nfor Graphical User Interaction"]

    node [shape = oval]

    reptile_from_reptile [label = "Client Program\nfor Graphical User Interaction"]
  }

  subgraph SUBGRAPH(scales) {
    label = "Component\nScales"

    node [shape = box]

    scales [label = "Python Source\nfor Graphical User Interaction"]
    scales_from_plant [label = "Python Source\nfor Message Transmission"]

    node [shape = oval]

    scales_from_scales [label = "Client Proxy\nfor Graphical User Interaction"]
  }

  subgraph SUBGRAPH(truffle) {
    label = "Component\nTruffle"

    node [shape = box]

    truffle [label = "C++ Source\nfor Common Tasks"]

    node [shape = oval]

    truffle_from_truffle [label = "Utility Library\nfor Common Tasks"]
  }

  subgraph SUBGRAPH(fungus) {
    label = "Component\nFungus"

    node [shape = box]

    fungus [label = "C++ Source\nfor Numerical Computation"]

    node [shape = oval]

    fungus_from_fungus [label = "Server Library\nfor Numerical Computation"]
  }

  subgraph SUBGRAPH(spores) {
    label = "Component\nSpores"

    node [shape = box]

    spores [label = "C++ Source\nfor Message Interpretation"]
    spores_from_plant [label = "C++ Source\nfor Message Transmission"]

    node [shape = oval]

    spores_from_spores [label = "Server Proxy\nfor Numerical Computation"]
  }

  /* subgraph SUBGRAPH(ape) {
    label = "Component\nApe"
  } */

  subgraph SUBGRAPH(primate) {
    label = "Component\nPrimate"

    node [shape = box]

    primate [label = "OCaml Source\nfor Message Interpretation"]
    primate_from_plant [label = "OCaml Source\nfor Message Transmission"]

    node [shape = oval]

    primate_from_primate [label = "Broker\nfor Message Passing"]
  }

  /* subgraph SUBGRAPH(hair) {
    label = "Component\nHair"
  } */

#ifdef COMPILE
  edge [style = solid]

  bird -> ungulate_from_bird [label = "(1) Code Extraction"]
  plant -> fur_from_plant [label = "(1) Code Generation"]
  plant -> scales_from_plant [label = "(1) Code Generation"]
  plant -> spores_from_plant [label = "(1) Code Generation"]
  plant -> primate_from_plant [label = "(1) Code Generation"]
  camel -> camel_from_camel [label = "(1) Compilation"]
  camel_from_camel -> fur_from_fur [label = "(3) Linking"]
  camel_from_camel -> primate_from_primate [label = "(2) Linking"]
  ungulate -> ungulate_from_ungulate [label = "(2) Compilation"]
  ungulate_from_bird -> ungulate_from_ungulate [label = "(2) Compilation"]
  ungulate_from_ungulate -> fur_from_fur [label = "(3) Linking"]
  fur -> fur_from_fur [label = "(3) Compilation"]
  fur_from_plant -> fur_from_fur [label = "(3) Compilation"]
  fur_from_fur -> primate_from_primate [label = "(4) Connection", dir = both]
  snake -> snake_from_snake [label = "(4) Interpretation"]
  snake_from_snake -> scales_from_scales [label = "(4) Interpretation"]
  reptile -> reptile_from_reptile [label = "(4) Interpretation"]
  reptile_from_reptile -> scales_from_scales [label = "(4) Interpretation"]
  scales -> scales_from_scales [label = "(4) Interpretation"]
  scales_from_plant -> scales_from_scales [label = "(4) Interpretation"]
  scales_from_scales -> primate_from_primate [label = "(4) Connection", dir = both]
  truffle -> truffle_from_truffle [label = "(1) Compilation"]
  truffle_from_truffle -> spores_from_spores [label = "(2) Linking"]
  fungus -> fungus_from_fungus [label = "(1) Compilation"]
  fungus_from_fungus -> spores_from_spores [label = "(2) Linking"]
  spores -> spores_from_spores [label = "(2) Compilation"]
  spores_from_plant -> spores_from_spores [label = "(2) Compilation"]
  spores_from_spores -> primate_from_primate [label = "(4) Connection", dir = both]
  primate -> primate_from_primate [label = "(2) Compilation"]
  primate_from_plant -> primate_from_primate [label = "(2) Compilation"]
#endif

#ifdef RUN
  edge [style = dashed]

  reptile_from_reptile -> scales_from_scales [label = "(5) Problem\nas Python Object"]
  scales_from_scales -> primate_from_primate [label = "(6) Problem\nas Thrift Message"]
  primate_from_primate -> fur_from_fur [label = "(7) Problem\nas Thrift Message"]
  fur_from_fur -> ungulate_from_ungulate [label = "(8) Problem\nas OCaml Object"]
  ungulate_from_ungulate -> fur_from_fur [label = "(9) Command\nas OCaml Object"]
  fur_from_fur -> primate_from_primate [label = "(10) Command\nas Thrift Message"]
  primate_from_primate -> spores_from_spores [label = "(11) Command\nas Thrift Message"]
  spores_from_spores -> fungus_from_fungus [label = "(12) Command\nas C++ Object"]
  fungus_from_fungus -> spores_from_spores [label = "(13) Result\nas C++ Object"]
  spores_from_spores -> primate_from_primate [label = "(14) Result\nas Thrift Message"]
  primate_from_primate -> fur_from_fur [label = "(15) Result\nas Thrift Message"]
  fur_from_fur -> ungulate_from_ungulate [label = "(16) Result\nas OCaml Object"]
  ungulate_from_ungulate -> fur_from_fur [label = "(17) Solution\nas OCaml Object"]
  fur_from_fur -> primate_from_primate [label = "(18) Solution\nas Thrift Message"]
  primate_from_primate -> scales_from_scales [label = "(19) Solution\nas Thrift Message"]
  scales_from_scales -> reptile_from_reptile [label = "(20) Solution\nas Python Object"]
#endif
}
