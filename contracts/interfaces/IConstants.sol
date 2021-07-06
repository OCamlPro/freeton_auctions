pragma ton-solidity >=0.44;

interface IConstants{

    struct Bidder{
        address bidder; // The bidder
        uint256 bid;
        address bid_contract;
        address bid_vault;
    }

    event Winner(address, uint256);
    event NoWinner();
    event Loser(address, uint256);
    event InvalidBid();
    event AuctionNotFinished();
    event BidCreated(address);
    event AuctionCreated(address);
    event BidPubkey(address auction, uint256 bid_id, uint256 bid_pubkey);
    event ThisIsYourBid(address auction, uint256 bid_id, address bid);
    event Ok();

}