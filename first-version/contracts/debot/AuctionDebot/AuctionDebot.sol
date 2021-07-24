pragma ton-solidity >=0.35.0;

pragma AbiHeader expire;
pragma AbiHeader time;
pragma AbiHeader pubkey;

import "lib/Debot.sol";
import "lib/Terminal.sol";
import "lib/AddressInput.sol";
import "lib/AmountInput.sol";
import "lib/ConfirmInput.sol";
import "lib/Sdk.sol";
import "lib/Menu.sol";
import "lib/Upgradable.sol";
import "lib/Transferable.sol";

// Interface of the contract with which to interact

interface IContract {
  function setter ( uint256 x ) external ;
  function getter () external returns ( uint256 y ) ;
}

abstract contract Utility {

  function tonsToStr(uint128 nanotons) internal pure returns (string) {
    (uint64 dec, uint64 float) = _tokens(nanotons);
    string floatStr = format("{}", float);
    while (floatStr.byteLength() < 9) {
      floatStr = "0" + floatStr;
    }
    return format("{}.{}", dec, floatStr);
  }

  function _tokens(uint128 nanotokens) internal pure
    returns (uint64, uint64) {
    uint64 decimal = uint64(nanotokens / 1e9);
    uint64 float = uint64(nanotokens - (decimal * 1e9));
    return (decimal, float);
  }
}

contract AuctionDebot is Debot, Upgradable, Transferable, Utility {

  string constant debot_name = "AuctionDebot" ;
  string constant debot_publisher = "My Software Company" ;
  string constant debot_caption = "Debot of Auction contracts" ;
  string constant debot_author = "My Software Company" ;
  string constant debot_language = "en" ;
  // your address with 0x instead of 0:
  uint8 constant debot_version_major = 1 ;
  uint8 constant debot_version_minor = 0 ;
  uint8 constant debot_version_fix = 0 ;
  uint256 constant debot_support =
    0x66e01d6df5a8d7677d9ab2daf7f258f1e2a7fe73da5320300395f99e01dc3b5f ;

  string constant debot_hello =
    "Hi, I will help you work with Auction contracts";

  address g_contract ;
  uint128 g_balance ;
  uint32 g_retryId ;
  bytes m_icon;


  address static s_auction_root; // The auction root
  bool m_reverse; // Is the auction on its reverse form?
  address m_root_wallet;
  address m_winner_processor;
  uint256 m_start_price;

  // Dutch specific variables
  uint256 m_dutch_end_price;
  uint256 m_dutch_price_delta;
  uint256 m_dutch_time_delta;

  // English specific variables
  uint256 m_english_max_tick;
  uint256 m_english_max_time;

  function askContractAddress() public {
    AddressInput.get(tvm.functionId(startChecks),
                     "Which contract do you want to work with?");
  }

  function startChecks(address value) public {
    Sdk.getAccountType(tvm.functionId(checkStatus), value);
    g_contract = value;
  }

  function checkStatus(int8 acc_type) public {
    if (!_checkActiveStatus(acc_type, "Contract")) {
      askContractAddress ();
    } else {
      Sdk.getAccountCodeHash(tvm.functionId(checkContractHash), g_contract);
    }
  }

  function _checkActiveStatus(int8 acc_type, string obj)
    private returns (bool) {
    if (acc_type == -1)  {
      Terminal.print(0, obj + " is inactive");
      return false;
    }
    if (acc_type == 0) {
      Terminal.print(0, obj + " is uninitialized");
      return false;
    }
    if (acc_type == 2) {
      Terminal.print(0, obj + " is frozen");
      return false;
    }
    return true;
  }

  function checkContractHash(uint256 code_hash) public {
    // compare with the expected code_hash
    if ( code_hash != 0x1111111111111111111111111111 ) {
      askContractAddress();
    } else {
      _gotoMainMenu();
    }
  }

  function _gotoMainMenu() public  {
    Sdk.getBalance(tvm.functionId(printMainMenu), g_contract );
  }

  function printMainMenu( uint128 nanotokens ) public {
    g_balance = nanotokens;
    string str = format("This wallet has {} tokens on the balance.",
                        tonsToStr(g_balance) );
    Terminal.print(0, str);

    MenuItem[] items;
    items.push( MenuItem("Change Contract", "",
                         tvm.functionId(askContractAddress)) );
    items.push( MenuItem("Call Getter", "",
                         tvm.functionId(callGetter)) );
    Menu.select("What's next?", "", items);
  }

  function callGetter() public {
    optional(uint256) pubkey = 0;
    g_retryId = tvm.functionId(callGetter);
    IContract(g_contract).getter{
        abiVer: 2,
        extMsg: true,
        sign: true,
        pubkey: pubkey,
        time: uint64(now),
        expire: 0,
        callbackId: tvm.functionId(onSuccess),
        onErrorId: tvm.functionId(onError)
        }() ;
  }

  function onError(uint32 sdkError, uint32 exitCode) public {
    exitCode = exitCode; sdkError = sdkError;
    ConfirmInput.get(g_retryId,
                     "Transaction failed. Do you want to retry transaction?");
  }

  function onSuccess(uint256 y) public {
    Terminal.print(0, format("Contract returned {}", y) );
    _gotoMainMenu () ;
  }
  
  //
  // Functions for external or internal invoke.
  //
  
  function other_entry(uint64 x) public pure returns (uint64 y) {
    y = x ;
  }
  

  //
  // Standard functions
  //
  
  function onCodeUpgrade() internal override {
    tvm.resetStorage();
  }
  
  function setIcon(bytes icon) public {
    require(msg.pubkey() == tvm.pubkey(), 100);
      tvm.accept();
      m_icon = icon;
  }
  
  /// @notice Returns Metadata about DeBot.
  function getDebotInfo() public functionID(0xDEB)
    override view
    returns(
            string name, string version, string publisher, string caption,
            string author, address support, string hello, string language,
            string dabi, bytes icon
            ) {
    name = debot_name;
    version = format("{}.{}.{}",
                     debot_version_major,
                     debot_version_minor,
                     debot_version_fix);
    publisher = debot_publisher ;
    caption = debot_caption ;
    author = debot_author ;
    support = address.makeAddrStd(0, debot_support);
    hello = debot_hello ;
    language = debot_language ;
    dabi = m_debotAbi.get();
    icon = m_icon;
  }
  
  function getRequiredInterfaces() public view override
    returns (uint256[] interfaces) {
    return [
            Terminal.ID,
            AmountInput.ID,
            ConfirmInput.ID,
            AddressInput.ID,
            Menu.ID ];
  }

  function setRootWallet(string value, string cont_msg, uint32 onSuccessID, uint32 onErrorID) internal {
        (uint res, bool status) = stoi("0x"+value);
        if (status){
            m_root_wallet = address(res);
            Terminal.input(onSuccessID,cont_msg,false);

        } else {
            Terminal.input(onErrorID,"Wrong wallet address! Try again",false);
        }
    }

  function setWinnerProcessor(string value, string cont_msg, uint32 onSuccessID, uint32 onErrorID) internal {
    (uint res, bool status) = stoi("0x"+value);
    if (status){
      m_winner_processor = address(res);
      Terminal.input(onSuccessID,cont_msg,false);
    } else {
      Terminal.input(onErrorID,"Wrong winner processor! Try again",false);
    }
  }

  function setStartPrice(string value, string cont_msg, uint32 onSuccessID, uint32 onErrorID) internal {
    (uint256 res, bool status) = stoi(value);
    if (status){
      m_start_price = res;
      Terminal.input(onSuccessID,cont_msg,false);
    } else {
      Terminal.input(onErrorID,"Wrong start price! Try again",false);
    }
  }

  function setDutchEndPrice(string value, string cont_msg, uint32 onSuccessID, uint32 onErrorID) internal {
    (uint256 res, bool status) = stoi(value);
    if (status){ // todo: add init invariant check ?
      m_dutch_end_price = res;
      Terminal.input(onSuccessID,cont_msg,false);
    } else {
      Terminal.input(onErrorID,"Wrong end price! Try again",false);
    }
  }

  function setDutchPriceDelta(string value, string cont_msg, uint32 onSuccessID, uint32 onErrorID) internal {
    (uint256 res, bool status) = stoi(value);
    if (status){ // todo: add init invariant check ?
      m_dutch_price_delta = res;
      Terminal.input(onSuccessID,cont_msg,false);
    } else {
      Terminal.input(onErrorID,"Wrong price delta! Try again",false);
    }
  }

  function setDutchTimeDelta(string value, string cont_msg, uint32 onSuccessID, uint32 onErrorID) internal {
    (uint256 res, bool status) = stoi(value);
    if (status){ // todo: add init invariant check ?
      m_dutch_time_delta = res;
      Terminal.input(onSuccessID,cont_msg,false);
    } else {
      Terminal.input(onErrorID,"Wrong time delta! Try again",false);
    }
  }

  function setEnglishMaxTick(string value, string cont_msg, uint32 onSuccessID, uint32 onErrorID) internal {
    (uint256 res, bool status) = stoi(value);
    if (status){ // todo: add init invariant check ?
      m_english_max_tick = res;
      Terminal.input(onSuccessID,cont_msg,false);
    } else {
      Terminal.input(onErrorID,"Wrong max tick! Try again",false);
    }
  }

  function setEnglishMaxTime(string value, string cont_msg, uint32 onSuccessID, uint32 onErrorID) internal {
    (uint256 res, bool status) = stoi(value);
    if (status){ // todo: add init invariant check ?
      m_english_max_time = res;
      Terminal.input(onSuccessID,cont_msg,false);
    } else {
      Terminal.input(onErrorID,"Wrong max time! Try again",false);
    }
  }

    /// @notice Entry point function for DeBot.
  function start() public override {
    Terminal.print(0, "Hello and welcome to the auction room.");
    Terminal.print(0, "Please select an action.");
    Terminal.print(0, "1. Create an auction.");
    Terminal.print(0, "2. Manage an auction.");
    Terminal.print(0, "3. Participate in an auction.");
    Terminal.input(tvm.functionId(setUserMainAction), "Action: ", false);
  }

  function setUserMainAction(string value) public {
    if (value == "1"){
      handleCreateAuction();
    } else if (value == "2") {
      handleManageAuction();
    } else if (value == "3") {
      handleParticipateAuction();
    } else {
      Terminal.print(0, format("You have entered \"{}\", which is an invalid action.", value));
    }
  }

  function handleCreateAuction() internal {
    Terminal.print(0, "What kind of auction do you want to start?");
    Terminal.print(0, "1. English.");
    Terminal.print(0, "2. English Reverse.");
    Terminal.print(0, "3. Dutch.");
    Terminal.print(0, "4. Dutch Reverse.");
    Terminal.print(0, "0. Cancel.");
    Terminal.input(tvm.functionId(setUserCreate), "Action: ", false);
  }

  function setUserCreate(string value) public {
    if (value == "0"){
      start();
    } else if (value == "1"){
      m_reverse = false;
      createEnglishAuction();
    } else if (value == "2") {
      m_reverse = true;
      createEnglishAuction();
    } else if (value == "3") {
      m_reverse = false;
      createDutchAuction();
    } else if (value == "4") {
      m_reverse = true;
      createDutchAuction();
    } else {
      Terminal.print(0, format("You have entered \"{}\", which is an invalid action.", value));
    }
  }

  function createEnglishAuction() internal {
    Terminal.input(tvm.functionId(setWalletAddressEn),"Please enter the Root Wallet address",false);
  }

  function setWalletAddressEn(string value) public {
    setRootWallet(
      value, 
      "Please enter the Winner processor address.", 
      tvm.functionId(setWinnerProcessorEn), 
      tvm.functionId(setWalletAddressEn)
    );
  }

  function setWinnerProcessorEn(string value) public {
    setWinnerProcessor(
      value, 
      "Please enter the starting price", 
      tvm.functionId(setStartPriceEn), 
      tvm.functionId(setWinnerProcessorEn)
    );
  }

  function setStartPriceEn(string value) public {
    setStartPrice(
      value,
      "Please enter the max tick",
      tvm.functionId(setMaxTickEn),
      tvm.functionId(setStartPriceEn)
    );
  }

  function setMaxTickEn(string value) public {
    setEnglishMaxTick(
      value,
      "Please enter the auction end",
      tvm.functionId(setMaxTimeEn),
      tvm.functionId(setMaxTickEn)
    );
  }

  function setMaxTimeEn(string value) public {
    setEnglishMaxTick(
      value,
      "Please confirm to see the details of your auction [Y]es / [N]o",
      tvm.functionId(onSuccessEn),
      tvm.functionId(setMaxTimeEn)
    );
  }

  function onSuccessEn(string value) public {
    Terminal.print(0, value);
    Terminal.print(0, "Here are the details of your auction.");
    if (m_reverse) {
      Terminal.print(0, "Kind: Reverse English");
    } else {
      Terminal.print(0, "Kind: English");
    }
    Terminal.print(0, format("Root Wallet: \"{}\"", m_root_wallet));
    Terminal.print(0, format("Winner processor: \"{}\"", m_winner_processor));
    Terminal.print(0, format("Start price: \"{}\"", m_start_price));
    Terminal.print(0, format("Max tick: \"{}\"", m_english_max_tick));
    Terminal.print(0, format("Auction end: \"{}\"", m_english_max_time));
    Terminal.input(tvm.functionId(deployEnglishAuction), "You are about to create an auction. Please confirm [Y]es / [N]o", false);
  }

  function deployEnglishAuction(string value) public {
    Terminal.print(0, value);
    Terminal.print(0, "TODO.");
  }

  function createDutchAuction() public {
    Terminal.print(0, "TODO.");
  }

  function handleManageAuction() internal {
    Terminal.print(0, "Please enter the auction address. TODO");
    //Terminal.input(tvm.functionId(setUserManage), "Action: ", false);
  }

  function handleParticipateAuction() internal {
    Terminal.print(0, "Please enter the auction address. TODO");
    // Terminal.input(tvm.functionId(setUserParticipate), "Action: ", false);
  }

}
