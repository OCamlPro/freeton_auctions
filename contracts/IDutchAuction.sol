pragma ton-solidity >=0.44;

interface IDutchAuction {
    function buy() external;
    function endAuction() external;
}