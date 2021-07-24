pragma ton-solidity >=0.44;

import "Constants.sol";
import "interfaces/IVault.sol";
import "interfaces/IProcessWinner.sol";

contract CrystalProcessWinner is IProcessWinner, Constants{
    
    address static s_seller;

    constructor() public{
        tvm.accept();
    }

    function acknowledgeWinner ( Bidder b ) external override {
        tvm.accept();
        emit Winner(b.bidder, b.bid);
    }

    function acknowledgeNoWinner() external override {
        tvm.accept();
        emit NoWinner();
    }

}