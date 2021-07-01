pragma ton-solidity >=0.44;

contract Constants {
    
    struct Bidder{
        address bidder; // The bidder
        uint128 bid;
    }

    event Winner(address, uint128);
    event NoWinner();
    event InvalidBid();
    event AuctionNotFinished();
    event BidCreated(address);
    event AuctionCreated(address);
    event BidPubkey(address auction, uint256 bid_id, uint256 bid_pubkey);
    event ThisIsYourBid(address auction, uint256 bid_id, address bid);
    event Ok();

    uint16 constant E_UNAUTHORIZED = 101;
    uint16 constant E_AUCTION_OVER = 102;
    uint16 constant E_UNINITIALIZED_PUBKEY = 103;
    uint16 constant E_BAD_PUBKEY = 104;
    uint16 constant E_ALREADY_INITIALIZED = 105;
    uint16 constant E_INVALID_BID = 106;
}