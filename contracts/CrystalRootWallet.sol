pragma ton-solidity >=0.44;

import "IRootWallet.sol";

contract CrystalRootWallet is IRootWallet{
    constructor() public{
        tvm.accept();
    }

    function getWalletAddress
        (
            int8 workchainId, 
            uint256 pubkey
        ) external override responsible returns(address){
        return address.makeAddrStd(workchainId, pubkey);
    }
}