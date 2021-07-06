pragma ton-solidity >=0.44;

interface IAuction {

    // Starts the bid process
    function bid(uint256) external;

    // Validates a bid.
    // This can only be called by a Bid contract
    function validateBid(address bidder, address bidder_vault, uint256 commitment) external;
    
    // Ends an auction if it is in a final state.
    function endAuction() external;
}