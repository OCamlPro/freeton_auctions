pragma ton-solidity >=0.44;

interface IDutchAuction {
    function bid() external;
    function endAuction() external;
}