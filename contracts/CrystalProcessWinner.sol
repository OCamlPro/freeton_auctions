pragma ton-solidity >=0.44;

import "Constants.sol";
import "IVault.sol";
import "IProcessWinner.sol";

contract CrystalProcessWinner is IProcessWinner, Constants{
    
    address static s_seller;

    constructor() public{
        tvm.accept();
    }

    function acknowledgeWinner ( Bidder b ) external override {
        tvm.accept();
        IVault(b.bid_vault).transfer(s_seller, b.amount, 100000);
        emit Winner(b.bidder, b.bid);
    }

    function acknowledgeLoser ( Bidder b ) external override {
        tvm.accept();
        IVault(b.bid_vault).transfer(b.bidder, b.amount, 100000);
        emit Loser(b.bidder, b.amount);
    }


    function acknowledgeNoWinner() external override {
        tvm.accept();
        emit NoWinner();
    }

}