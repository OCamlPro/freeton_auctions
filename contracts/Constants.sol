pragma ton-solidity >=0.44;

contract Constants {
    
    struct Bidder{
        address bidder; // The bidder
        uint32 callbackRefundFunctionId; // The function to call if refund
        uint32 callbackWinnerFunctionId; // The function to call if winner
        uint128 bid;
    }

    event InvalidBid();
    event AuctionNotFinished();

    uint16 constant E_UNAUTHORIZED = 101;
}