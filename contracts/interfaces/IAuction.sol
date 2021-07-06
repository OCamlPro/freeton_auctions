pragma ton-solidity >=0.44;

interface IAuction {
    function bid(uint256) external;
    function validateBid(address bidder, address bidder_vault, uint256 commitment) external;
    function endAuction() external;
}