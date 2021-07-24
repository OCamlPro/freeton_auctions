pragma ton-solidity >=0.44;

interface IVault {
    function transfer(address dest, uint256 tokens, uint128 grams) external;
    function getBalance() responsible  external returns(uint256);
}
