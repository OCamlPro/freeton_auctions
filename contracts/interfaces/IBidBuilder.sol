pragma ton-solidity >=0.44;

interface IBidBuilder{
    function init(address bid_address, address auction_addr) external;
    function deployBid(uint256) external;
    function validateBid(address bidder, address vault_address, uint256 commitment, uint256 bid_id) external view;
}