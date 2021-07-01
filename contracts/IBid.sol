pragma ton-solidity >=0.44;

interface IBid {
    function submit() external;
    function thisIsMyCode() external responsible returns(TvmCell);
}