pragma ton-solidity >=0.44;

interface IAuction {
    function bid(uint256) external;
    function validateBid(address bidder, uint256 commitment) external;
}