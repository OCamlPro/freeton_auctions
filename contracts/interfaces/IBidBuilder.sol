pragma ton-solidity >=0.44;

interface IBidBuilder{
    function init(address, address) external;
    function deployBid(uint256) external;
    function validateBid(address bidder, address vault_address, uint256 commitment, uint256 bid_id) external view;
}