pragma ton-solidity >=0.44;

import "VEnglishAuction.sol";
import "Constants.sol";
import "interfaces/IAuction.sol";

contract EnglishReverseAuction is Constants, IAuction, VEnglishAuction {
    function newBidIsBetterThan(uint256 old_bid, uint256 new_bid) internal override returns (bool){
        return (new_bid < old_bid);
    }

    function processWinner(Bidder b) internal override {
        IProcessWinner(b.bid_process_winner).
            acknowledgeWinner{value:0.2 ton}(b);
        IBid(b.bid_contract).transferVaultContent{value:0.2 ton}(b.bidder, b.bid);
    }
}