pragma ton-solidity >=0.44;

interface IReverseBidBuilder{
    function init(address, address, address) external;
    function deployBid(uint256, address) external;
    function validateBid(address bidder, address vault_address, uint256 commitment, uint256 bid_id, address winner_processor) external view;
}