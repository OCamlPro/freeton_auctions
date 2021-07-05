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
        IVault(b.bid_vault).transfer{value:0, flag: 128}(s_seller, b.bid, 100000);
        emit Winner(b.bidder, b.bid);
    }

    function acknowledgeLoser ( Bidder b ) external override {
        tvm.accept();
        IVault(b.bid_vault).transfer{value:0, flag: 128}(b.bidder, b.bid, 100000);
        emit Loser(b.bidder, b.bid);
    }


    function acknowledgeNoWinner() external override {
        tvm.accept();
        emit NoWinner();
    }

}