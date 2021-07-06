pragma ton-solidity >=0.44;

import "Bid.sol";
import "Constants.sol";
import "Buildable.sol";
import "interfaces/IBidBuilder.sol";

contract BidBuilder is Constants, Buildable, IBidBuilder {

    optional(TvmCell) bid_code; // Code of the bid contract, to be initialized
    optional(address) auction_address; // Auction address, to be initialized

    address static s_root_wallet; // Wallet root
    uint256 static s_auction_id; // Auction id (useful for address uniqueness)
    uint256 id; // Id for the created bids

    modifier uninitializedCell(optional(TvmCell) opt){
        require (!opt.hasValue(), E_ALREADY_INITIALIZED);
        _;
    }

    modifier uninitializedAddr(optional(address) opt){
        require (!opt.hasValue(), E_ALREADY_INITIALIZED);
        _;
    }

    modifier initializedCell(optional(TvmCell) opt){
        require (opt.hasValue(), E_UNINITIALIZED);
        _;
    }

    modifier initializedAddr(optional(address) opt){
        require (opt.hasValue(), E_UNINITIALIZED);
        _;
    }

    function setCode(TvmCell code) uninitializedCell(bid_code) external{
        tvm.accept();
        bid_code = code;
        emit Ok();
    }

    function init(address bid_address, address auction_addr) 
        override external uninitializedAddr(auction_address){
        
        tvm.accept();
        auction_address.set(auction_addr);
        IBuildable(bid_address).thisIsMyCode{value:0.5 ton, callback:this.setCode}();
    
    }

    constructor() public{
        tvm.accept();
        id = 0;
    }

    // For English/Dutch auctions, commitment = amount
    function deployBid(uint256 commitment) override external 
        initializedAddr(auction_address)
        initializedCell(bid_code) {
        tvm.accept();
        Bid b =
            new Bid
            {
                value:0,
                flag: 128,
                code: bid_code.get(),
                pubkey: msg.pubkey(),
                varInit: 
                {
                    s_auction: auction_address.get(),
                    s_bidder: msg.sender,
                    s_commitment: commitment,
                    s_id: id,
                    s_root_wallet: s_root_wallet
                }
            }();
        ++id;
        emit ThisIsYourBid(auction_address.get(), id, address(b));
    }
}