#ifdef CLUSTER
#define SUBGRAPH(x) cluster_##x
#else
#define SUBGRAPH(x) uncluster_##x
#endif

digraph habitat {
  /* subgraph SUBGRAPH(bird) {
    label = "Component\nBird"
  } */

  subgraph SUBGRAPH(fowl) {
    label = "Component\nFowl"

    node [shape = box]

    fowl [label = "Coq Source\nfor Formal Specification"]
  }

  /* subgraph SUBGRAPH(feathers) {
    label = "Component\nFeathers"
  } */

  /* subgraph SUBGRAPH(plant) {
    label = "Component\nPlant"
  } */

  subgraph SUBGRAPH(flower) {
    label = "Component\nFlower"

    node [shape = box]

    flower [label = "Thrift IDL Source\nfor Message Specification"]
  }

  /* subgraph SUBGRAPH(leaves) {
    label = "Component\nLeaves"
  } */

  subgraph SUBGRAPH(ungulate) {
    label = "Component\nUngulate"

    node [shape = box]

    ungulate [label = "OCaml Source\nfor Common Tasks"]

    node [shape = oval]

    ungulate_from_ungulate [label = "Utility Library\nfor Common Tasks"]
  }

  subgraph SUBGRAPH(camel) {
    label = "Component\nCamel"

    node [shape = box]

    camel [label = "OCaml Source\nfor Symbolic Manipulation"]
    camel_from_fowl [label = "OCaml Source\nfor Formal Verification"]

    node [shape = oval]

    camel_from_camel [label = "Server Library\nfor Verified Symbolic Manipulation"]
  }

  subgraph SUBGRAPH(fur) {
    label = "Component\nFur"

    node [shape = box]

    fur [label = "OCaml Source\nfor Message Interpretation"]
    fur_from_flower [label = "OCaml Source\nfor Message Transmission"]

    node [shape = oval]

    fur_from_fur [label = "Server Proxy\nfor Verified Symbolic Manipulation"]
  }

  subgraph SUBGRAPH(reptile) {
    label = "Component\nReptile"

    node [shape = box]

    reptile [label = "Python Source\nfor Common Tasks"]

    node [shape = oval]

    reptile_from_reptile [label = "Utility Library\nfor Common Tasks"]
  }

  subgraph SUBGRAPH(snake) {
    label = "Component\nSnake"

    node [shape = box]

    snake [label = "Python Source\nfor Graphical User Interaction"]

    node [shape = oval]

    snake_from_snake [label = "Client Program\nfor Graphical User Interaction"]
  }

  subgraph SUBGRAPH(scales) {
    label = "Component\nScales"

    node [shape = box]

    scales [label = "Python Source\nfor Graphical User Interaction"]
    scales_from_flower [label = "Python Source\nfor Message Transmission"]

    node [shape = oval]

    scales_from_scales [label = "Client Proxy\nfor Graphical User Interaction"]
  }

  subgraph SUBGRAPH(fungus) {
    label = "Component\nFungus"

    node [shape = box]

    fungus [label = "C++ Source\nfor Common Tasks"]

    node [shape = oval]

    fungus_from_fungus [label = "Utility Library\nfor Common Tasks"]
  }

  subgraph SUBGRAPH(truffle) {
    label = "Component\nTruffle"

    node [shape = box]

    truffle [label = "C++ Source\nfor Numerical Computation"]

    node [shape = oval]

    truffle_from_truffle [label = "Server Library\nfor Numerical Computation"]
  }

  subgraph SUBGRAPH(spores) {
    label = "Component\nSpores"

    node [shape = box]

    spores [label = "C++ Source\nfor Message Interpretation"]
    spores_from_flower [label = "C++ Source\nfor Message Transmission"]

    node [shape = oval]

    spores_from_spores [label = "Server Proxy\nfor Numerical Computation"]
  }

  /* subgraph SUBGRAPH(primate) {
    label = "Component\nPrimate"
  } */

  subgraph SUBGRAPH(ape) {
    label = "Component\nApe"

    node [shape = box]

    ape [label = "OCaml Source\nfor Message Interpretation"]
    ape_from_flower [label = "OCaml Source\nfor Message Transmission"]

    node [shape = oval]

    ape_from_ape [label = "Broker\nfor Message Passing"]
  }

  /* subgraph SUBGRAPH(hair) {
    label = "Component\nHair"
  } */

#ifdef COMPILE
  edge [style = solid]

  fowl -> camel_from_fowl [label = "(1) Code Extraction"]
  flower -> fur_from_flower [label = "(1) Code Generation"]
  flower -> scales_from_flower [label = "(1) Code Generation"]
  flower -> spores_from_flower [label = "(1) Code Generation"]
  flower -> ape_from_flower [label = "(1) Code Generation"]
  ungulate -> ungulate_from_ungulate [label = "(1) Compilation"]
  fungus -> fungus_from_fungus [label = "(1) Compilation"]
  truffle -> truffle_from_truffle [label = "(1) Compilation"]

  ungulate_from_ungulate -> ape_from_ape [label = "(2) Linking"]
  camel -> camel_from_camel [label = "(2) Compilation"]
  camel_from_fowl -> camel_from_camel [label = "(2) Compilation"]
  fungus_from_fungus -> spores_from_spores [label = "(2) Linking"]
  truffle_from_truffle -> spores_from_spores [label = "(2) Linking"]
  spores -> spores_from_spores [label = "(2) Compilation"]
  spores_from_flower -> spores_from_spores [label = "(2) Compilation"]
  ape -> ape_from_ape [label = "(2) Compilation"]
  ape_from_flower -> ape_from_ape [label = "(2) Compilation"]

  ungulate_from_ungulate -> fur_from_fur [label = "(3) Linking"]
  camel_from_camel -> fur_from_fur [label = "(3) Linking"]
  fur -> fur_from_fur [label = "(3) Compilation"]
  fur_from_flower -> fur_from_fur [label = "(3) Compilation"]

  fur_from_fur -> ape_from_ape [label = "(4) Connection", dir = both]
  reptile -> reptile_from_reptile [label = "(4) Interpretation"]
  reptile_from_reptile -> scales_from_scales [label = "(4) Interpretation"]
  snake -> snake_from_snake [label = "(4) Interpretation"]
  snake_from_snake -> scales_from_scales [label = "(4) Interpretation"]
  scales -> scales_from_scales [label = "(4) Interpretation"]
  scales_from_flower -> scales_from_scales [label = "(4) Interpretation"]
  scales_from_scales -> ape_from_ape [label = "(4) Connection", dir = both]
  spores_from_spores -> ape_from_ape [label = "(4) Connection", dir = both]
#endif

#ifdef RUN
  edge [style = dashed]

  snake_from_snake -> scales_from_scales [label = "(5) Problem\nas Python Object"]
  scales_from_scales -> ape_from_ape [label = "(6) Problem\nas Thrift Message"]
  ape_from_ape -> fur_from_fur [label = "(7) Problem\nas Thrift Message"]
  fur_from_fur -> camel_from_camel [label = "(8) Problem\nas OCaml Object"]
  camel_from_camel -> fur_from_fur [label = "(9) Command\nas OCaml Object"]
  fur_from_fur -> ape_from_ape [label = "(10) Command\nas Thrift Message"]
  ape_from_ape -> spores_from_spores [label = "(11) Command\nas Thrift Message"]
  spores_from_spores -> truffle_from_truffle [label = "(12) Command\nas C++ Object"]
  truffle_from_truffle -> spores_from_spores [label = "(13) Result\nas C++ Object"]
  spores_from_spores -> ape_from_ape [label = "(14) Result\nas Thrift Message"]
  ape_from_ape -> fur_from_fur [label = "(15) Result\nas Thrift Message"]
  fur_from_fur -> camel_from_camel [label = "(16) Result\nas OCaml Object"]
  camel_from_camel -> fur_from_fur [label = "(17) Solution\nas OCaml Object"]
  fur_from_fur -> ape_from_ape [label = "(18) Solution\nas Thrift Message"]
  ape_from_ape -> scales_from_scales [label = "(19) Solution\nas Thrift Message"]
  scales_from_scales -> snake_from_snake [label = "(20) Solution\nas Python Object"]
#endif

  edge [style = invis]

  ungulate_from_ungulate -> camel
  reptile_from_reptile -> snake
  fungus_from_fungus -> truffle

  camel_from_camel -> fur
  snake_from_snake -> scales
  truffle_from_truffle -> spores

  camel_from_camel -> flower -> fur
  snake_from_snake -> flower -> scales
  truffle_from_truffle -> flower -> spores

  fur_from_fur -> ape
  scales_from_scales -> ape
  spores_from_spores -> ape
}
