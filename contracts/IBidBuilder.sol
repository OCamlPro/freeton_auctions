pragma ton-solidity >=0.44;

interface IBidBuilder{
    function init(address) external;
    function deployBid(address, uint256) external;
}