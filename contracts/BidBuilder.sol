pragma ton-solidity >=0.44;

import "Bid.sol";
import "Constants.sol";
import "Buildable.sol";
import "IBidBuilder.sol";

contract BidBuilder is Constants, Buildable, IBidBuilder {

    optional(TvmCell) s_bid_code; // Code of the bid contract
    address static s_root_wallet; // Wallet root
    uint256 id; // Id for the created bids

    constructor() public{
        tvm.accept();
        id = 0;
    }

    modifier uninitialized(optional(TvmCell) v){
        require (!v.hasValue(), E_ALREADY_INITIALIZED);
        _;
    }

    function setCode(TvmCell code) uninitialized(s_bid_code) external{
        tvm.accept();
        s_bid_code = code;
        emit Ok();
    }

    function init(address bid) override external{
        tvm.accept();
        Bid(bid).thisIsMyCode{value: 1 ton, callback:this.setCode}();
    }

    // For English/Dutch auctions, commitment = amount
    // For Blind auction, commitment = hash
    function deployBid(address auction, uint256 commitment) override external{
        tvm.accept();
        Bid b =
            new Bid
            {
            value: 5 ton,
            code: s_bid_code.get(),
            pubkey: msg.pubkey(),
            varInit: 
                {
                    s_auction: auction,
                    s_bidder: msg.sender,
                    s_commitment: commitment,
                    s_id: id,
                    s_root_wallet: s_root_wallet
                }
            }();
        ++id;
        emit ThisIsYourBid(auction, id, address(b));
    }

}