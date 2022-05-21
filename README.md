Isolation theorems of the framework:
* Preservation of the invariant:
 formalization/dma_framework/lemmas/l4/invariant_l4_preservationScript.sml:SYSTEM_PRESERVES_INVARIANT_L4_LEMMA
* Issued memory requests address readable and writable memory:
 formalization/dma_framework/lemmas/l4/memory_isolationScript.sml:DMA_READ_WRITE_LEMMA

Isolation theorems of the BBB USB instantiation:
* Preservation of the invariant:
 formalization/dma_framework/instantiations/bbb-usb/bbb_usb_isolationScript.sml:BBB_USB_PRESERVES_INVARIANT_L4_LEMMA
* Issued memory requests address readable and writable memory:
 formalization/dma_framework/instantiations/bbb-usb/bbb_usb_isolationScript.sml:BBB_USB_DMA_READ_WRITE_LEMMA

Compilation on an ubuntu distribution:
* Compilation of the framework: Go to formalization/dma_framework/lemmas/l4/ and type sh compile.sh in the terminal.
* Compilation of the BBB USB instantiation: Go to formalization/dma_framework/instantiations/bbb-usb/ and type sh compile.sh in the terminal.

The core files of the framework are:
* formalization/dma_framework/definitions/framework/stateScript.sml:
 The definitions of the data structures used in the framework, including comments for the functions to be instantiated.
* formalization/dma_framework/definitions/framework/operationsScript.sml:
 The definitions of the operations of the framework.
* formalization/dma_framework/definitions/framework/proof_obligationsScript.sml:
 The definitions of the proof obligations of the framework, including comments.
* formalization/dma_framework/lemmas/:
 Folders containing different types of lemmas, including the lemmas for each of the four abstraction layers.
