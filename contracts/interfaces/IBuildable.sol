pragma ton-solidity >=0.44;

interface IBuildable{
    function thisIsMyCode() external responsible returns(TvmCell);
}