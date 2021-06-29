pragma ton-solidity >=0.44;

interface IAuction {
    function bid() external;
    function thisIsMyCode() external responsible returns(TvmCell);
}