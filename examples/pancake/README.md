# Front-running in PancakeSwap AMM
*This project is part of a Masters thesis at the IT University of Copenhagen by Mathias Malling Jensen under the supervision of Alessandro Bruni.*

The purpose of the project is to explore and prove the existence of Front-running attacks in the PancakeSwap AMM. In this example, we model the PancakeSwap AMM as defined in the PancakeSwap repository:
[PancakeSwap Smart Contracts](https://github.com/pancakeswap/pancake-smart-contracts/tree/master/projects/exchange-protocol/contracts)

To prove the existence of possible Front-running attacks, we have converted the existing Solidity code as seen on the BSC network into the Coq/ConCert framework. The resulting implementation in the ConCert framework aims to be as close as possible to the implemented Solidity code. As we are solely interested in exploring the front-running attack, some parts (adding/removing liquidity) have been omitted in our implementation.

The implemented model is accompanied by several lemmas/proofs that shows the model's functional correctness and ultimately that a front-running attack is possible.

All code (specification and proofs) are currently in [Pancake.V](https://github.com/Mallingo/ConCert/blob/master/examples/pancake/Pancake.v). Will be refactored at a later stage.

### Limitations
- Allows for creation of a single AMM pair (in the same context).
- Code extraction not supported
