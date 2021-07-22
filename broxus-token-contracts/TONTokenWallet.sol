// This file was generated from file "TONTokenWallet.spp". DO NOT EDIT !
pragma ton-solidity >= 0.32.0;

pragma AbiHeader expire;
pragma AbiHeader pubkey;
interface IDestroyable  {
  function destroy(address gas_dest) external;
}

interface AllowanceInfoStructure  {
  struct AllowanceInfo {
    uint128 remaining_tokens;
    address spender;
  }
}

interface ITONTokenWallet is AllowanceInfoStructure {
  struct ITONTokenWalletDetails {
    address root_address;
    uint256 wallet_public_key;
    address owner_address;
    uint128 balance;
    address receive_callback;
    address bounced_callback;
    bool allow_non_notifiable;
  }
  function getDetails() external view responsible returns (ITONTokenWalletDetails);
  function getWalletCode() external view responsible returns (TvmCell);
  function accept(uint128 tokens) external;
  function balance() external view responsible returns (uint128);
  function allowance() external view responsible returns (AllowanceInfo);
  function approve(address spender, uint128 remaining_tokens, uint128 tokens) external;
  function disapprove() external;
  function setReceiveCallback(address receive_callback, bool allow_non_notifiable) external;
  function setBouncedCallback(address bounced_callback) external;
  function transfer(address to, uint128 tokens, uint128 grams, address send_gas_to, bool notify_receiver, TvmCell payload) external;
  function transferFrom(address from, address to, uint128 tokens, uint128 grams, address send_gas_to, bool notify_receiver, TvmCell payload) external;
  function transferToRecipient(uint256 recipient_public_key, address recipient_address, uint128 tokens, uint128 deploy_grams, uint128 transfer_grams, address send_gas_to, bool notify_receiver, TvmCell payload) external;
  function internalTransfer(uint128 tokens, uint256 sender_public_key, address sender_address, address send_gas_to, bool notify_receiver, TvmCell payload) external;
  function internalTransferFrom(address to, uint128 tokens, address send_gas_to, bool notify_receiver, TvmCell payload) external;
}

interface IBurnableByOwnerTokenWallet  {
  function burnByOwner(uint128 tokens, uint128 grams, address send_gas_to, address callback_address, TvmCell callback_payload) external;
}

interface IBurnableByRootTokenWallet  {
  function burnByRoot(uint128 tokens, address send_gas_to, address callback_address, TvmCell callback_payload) external;
}

interface IBurnableTokenRootContract  {
  function tokensBurned(uint128 tokens, uint256 sender_public_key, address sender_address, address send_gas_to, address callback_address, TvmCell callback_payload) external;
}

interface ITokenWalletDeployedCallback  {
  function notifyWalletDeployed(address root) external;
}

interface ITokensReceivedCallback  {
  function tokensReceivedCallback(address token_wallet, address token_root, uint128 amount, uint256 sender_public_key, address sender_address, address sender_wallet, address original_gas_to, uint128 updated_balance, TvmCell payload) external;
}

interface ITokensBouncedCallback  {
  function tokensBouncedCallback(address token_wallet, address token_root, uint128 amount, address bounced_from, uint128 updated_balance) external;
}

library TONTokenWalletErrors  {
  uint8 constant error_message_sender_is_not_my_owner = 100 ;
  uint8 constant error_not_enough_balance = 101 ;
  uint8 constant error_message_sender_is_not_my_root = 102 ;
  uint8 constant error_message_sender_is_not_good_wallet = 103 ;
  uint8 constant error_wrong_bounced_header = 104 ;
  uint8 constant error_wrong_bounced_args = 105 ;
  uint8 constant error_non_zero_remaining = 106 ;
  uint8 constant error_no_allowance_set = 107 ;
  uint8 constant error_wrong_spender = 108 ;
  uint8 constant error_not_enough_allowance = 109 ;
  uint8 constant error_low_message_value = 110 ;
  uint8 constant error_wrong_recipient = 111 ;
  uint8 constant error_recipient_has_disallow_non_notifiable = 112 ;
}

library TONTokenWalletConstants  {
  uint128 constant target_gas_balance = 0.5 ton;
}

interface IVersioned  {
  function getVersion() external pure responsible returns (uint32);
}

contract TONTokenWallet is ITONTokenWallet, IDestroyable, IBurnableByOwnerTokenWallet, IBurnableByRootTokenWallet, IVersioned {
  address static root_address;
  TvmCell static code;
  uint256 static wallet_public_key;
  address static owner_address;
  uint128 balance_;
  optional (AllowanceInfo) allowance_;
  address receive_callback;
  address bounced_callback;
  bool allow_non_notifiable;
  constructor() public {
      require(((wallet_public_key == tvm.pubkey()) && ((owner_address.value == 0 ) || (wallet_public_key == 0 ))));
      tvm.accept();
      allow_non_notifiable = true;
      if ((owner_address.value != 0 ))
        {
            ITokenWalletDeployedCallback(owner_address).notifyWalletDeployed {value: 0.1 ton,flag: 1 }(root_address);
        }
  }
  function getVersion() external pure responsible override returns (uint32) {
      return  4 ;
  }
  function balance() external view responsible override returns (uint128) {
      return {value: 0 ,bounce: false,flag: 64 } balance_;
  }
  function getDetails() external view responsible override returns (ITONTokenWalletDetails) {
      return {value: 0 ,bounce: false,flag: 64 } ITONTokenWalletDetails(root_address, wallet_public_key, owner_address, balance_, receive_callback, bounced_callback, allow_non_notifiable);
  }
  function getWalletCode() external view responsible override returns (TvmCell) {
      return {value: 0 ,bounce: false,flag: 64 } code;
  }
  function accept(uint128 tokens) external override onlyRoot() {
      tvm.accept();
      balance_ += tokens;
  }
  function allowance() external view responsible override returns (AllowanceInfo) {
      return {value: 0 ,bounce: false,flag: 64 } (allowance_.hasValue() ? allowance_.get() : AllowanceInfo(0 , address.makeAddrStd(0 , 0 )));
  }
  function approve(address spender, uint128 remaining_tokens, uint128 tokens) external override onlyOwner() {
      require(((remaining_tokens == 0 ) || (! allowance_.hasValue())), TONTokenWalletErrors.error_non_zero_remaining);
      if ((owner_address.value != 0 ))
        {
            tvm.rawReserve(math.max(TONTokenWalletConstants.target_gas_balance, (address(this).balance - msg.value)), 2 );
        }
      else
        {
            tvm.accept();
        }
      if (allowance_.hasValue())
        {
            if ((allowance_.get().remaining_tokens == remaining_tokens))
              {
                  allowance_.set(AllowanceInfo(tokens, spender));
              }
        }
      else
        {
            allowance_.set(AllowanceInfo(tokens, spender));
        }
      if ((owner_address.value != 0 ))
        {
            msg.sender.transfer({value: 0 ,flag: 128 });
        }
  }
  function disapprove() external override onlyOwner() {
      if ((owner_address.value != 0 ))
        {
            tvm.rawReserve(math.max(TONTokenWalletConstants.target_gas_balance, (address(this).balance - msg.value)), 2 );
        }
      else
        {
            tvm.accept();
        }
      allowance_.reset();
      if ((owner_address.value != 0 ))
        {
            msg.sender.transfer({value: 0 ,flag: 128 });
        }
  }
  function transferToRecipient(uint256 recipient_public_key, address recipient_address, uint128 tokens, uint128 deploy_grams, uint128 transfer_grams, address send_gas_to, bool notify_receiver, TvmCell payload) external override onlyOwner() {
      require((tokens > 0 ));
      require((tokens <= balance_), TONTokenWalletErrors.error_not_enough_balance);
      require(((recipient_address.value == 0 ) || (recipient_public_key == 0 )), TONTokenWalletErrors.error_wrong_recipient);
      if ((owner_address.value != 0 ))
        {
            uint128 reserve = math.max(TONTokenWalletConstants.target_gas_balance, (address(this).balance - msg.value));
            require((address(this).balance > ((reserve + TONTokenWalletConstants.target_gas_balance) + deploy_grams)), TONTokenWalletErrors.error_low_message_value);
            require((recipient_address != owner_address), TONTokenWalletErrors.error_wrong_recipient);
            tvm.rawReserve(reserve, 2 );
        }
      else
        {
            require((address(this).balance > (deploy_grams + transfer_grams)), TONTokenWalletErrors.error_low_message_value);
            require((transfer_grams > TONTokenWalletConstants.target_gas_balance), TONTokenWalletErrors.error_low_message_value);
            require((recipient_public_key != wallet_public_key));
            tvm.accept();
        }
      TvmCell stateInit = tvm.buildStateInit({contr: TONTokenWallet,varInit:  {root_address: root_address,code: code,wallet_public_key: recipient_public_key,owner_address: recipient_address},pubkey: recipient_public_key,code: code});
      address to;
      if ((deploy_grams > 0 ))
        {
            to = new TONTokenWallet {stateInit: stateInit,value: deploy_grams,wid: address(this).wid,flag: 1 }();
        }
      else
        {
            to = address(tvm.hash(stateInit));
        }
      if ((owner_address.value != 0 ))
        {
            balance_ -= tokens;
            ITONTokenWallet(to).internalTransfer {value: 0 ,flag: 129 ,bounce: true}(tokens, wallet_public_key, owner_address, ((send_gas_to.value != 0 ) ? send_gas_to : owner_address), notify_receiver, payload);
        }
      else
        {
            balance_ -= tokens;
            ITONTokenWallet(to).internalTransfer {value: transfer_grams,flag: 1 ,bounce: true}(tokens, wallet_public_key, owner_address, ((send_gas_to.value != 0 ) ? send_gas_to : address(this)), notify_receiver, payload);
        }
  }
  function transfer(address to, uint128 tokens, uint128 grams, address send_gas_to, bool notify_receiver, TvmCell payload) external override onlyOwner() {
      require((tokens > 0 ));
      require((tokens <= balance_), TONTokenWalletErrors.error_not_enough_balance);
      require((to.value != 0 ), TONTokenWalletErrors.error_wrong_recipient);
      require((to != address(this)), TONTokenWalletErrors.error_wrong_recipient);
      if ((owner_address.value != 0 ))
        {
            uint128 reserve = math.max(TONTokenWalletConstants.target_gas_balance, (address(this).balance - msg.value));
            require((address(this).balance > (reserve + TONTokenWalletConstants.target_gas_balance)), TONTokenWalletErrors.error_low_message_value);
            tvm.rawReserve(reserve, 2 );
            balance_ -= tokens;
            ITONTokenWallet(to).internalTransfer {value: 0 ,flag: 129 ,bounce: true}(tokens, wallet_public_key, owner_address, ((send_gas_to.value != 0 ) ? send_gas_to : owner_address), notify_receiver, payload);
        }
      else
        {
            require((address(this).balance > grams), TONTokenWalletErrors.error_low_message_value);
            require((grams > TONTokenWalletConstants.target_gas_balance), TONTokenWalletErrors.error_low_message_value);
            tvm.accept();
            balance_ -= tokens;
            ITONTokenWallet(to).internalTransfer {value: grams,bounce: true,flag: 1 }(tokens, wallet_public_key, owner_address, ((send_gas_to.value != 0 ) ? send_gas_to : address(this)), notify_receiver, payload);
        }
  }
  function transferFrom(address from, address to, uint128 tokens, uint128 grams, address send_gas_to, bool notify_receiver, TvmCell payload) external override onlyOwner() {
      require((to.value != 0 ), TONTokenWalletErrors.error_wrong_recipient);
      require((tokens > 0 ));
      require((from != to), TONTokenWalletErrors.error_wrong_recipient);
      if ((owner_address.value != 0 ))
        {
            uint128 reserve = math.max(TONTokenWalletConstants.target_gas_balance, (address(this).balance - msg.value));
            require((address(this).balance > (reserve + (TONTokenWalletConstants.target_gas_balance * 2 ))), TONTokenWalletErrors.error_low_message_value);
            tvm.rawReserve(reserve, 2 );
            ITONTokenWallet(from).internalTransferFrom {value: 0 ,flag: 129 }(to, tokens, ((send_gas_to.value != 0 ) ? send_gas_to : owner_address), notify_receiver, payload);
        }
      else
        {
            require((address(this).balance > grams), TONTokenWalletErrors.error_low_message_value);
            require((grams > (TONTokenWalletConstants.target_gas_balance * 2 )), TONTokenWalletErrors.error_low_message_value);
            tvm.accept();
            ITONTokenWallet(from).internalTransferFrom {value: grams,flag: 1 }(to, tokens, ((send_gas_to.value != 0 ) ? send_gas_to : address(this)), notify_receiver, payload);
        }
  }
  function internalTransfer(uint128 tokens, uint256 sender_public_key, address sender_address, address send_gas_to, bool notify_receiver, TvmCell payload) external override {
      require(((notify_receiver || allow_non_notifiable) || (receive_callback.value == 0 )), TONTokenWalletErrors.error_recipient_has_disallow_non_notifiable);
      address expectedSenderAddress = getExpectedAddress(sender_public_key, sender_address);
      require((msg.sender == expectedSenderAddress), TONTokenWalletErrors.error_message_sender_is_not_good_wallet);
      require(((sender_address != owner_address) || (sender_public_key != wallet_public_key)), TONTokenWalletErrors.error_wrong_recipient);
      if ((owner_address.value != 0 ))
        {
            uint128 reserve = math.max(TONTokenWalletConstants.target_gas_balance, (address(this).balance - msg.value));
            require((address(this).balance > reserve), TONTokenWalletErrors.error_low_message_value);
            tvm.rawReserve(reserve, 2 );
        }
      else
        {
            tvm.rawReserve((address(this).balance - msg.value), 2 );
        }
      balance_ += tokens;
      if ((notify_receiver && (receive_callback.value != 0 )))
        {
            ITokensReceivedCallback(receive_callback).tokensReceivedCallback {value: 0 ,flag: 128 }(address(this), root_address, tokens, sender_public_key, sender_address, msg.sender, send_gas_to, balance_, payload);
        }
      else
        {
            send_gas_to.transfer({value: 0 ,flag: 128 });
        }
  }
  function internalTransferFrom(address to, uint128 tokens, address send_gas_to, bool notify_receiver, TvmCell payload) external override {
      require(allowance_.hasValue(), TONTokenWalletErrors.error_no_allowance_set);
      require((msg.sender == allowance_.get().spender), TONTokenWalletErrors.error_wrong_spender);
      require((tokens <= allowance_.get().remaining_tokens), TONTokenWalletErrors.error_not_enough_allowance);
      require((tokens <= balance_), TONTokenWalletErrors.error_not_enough_balance);
      require((tokens > 0 ));
      require((to != address(this)), TONTokenWalletErrors.error_wrong_recipient);
      if ((owner_address.value != 0 ))
        {
            uint128 reserve = math.max(TONTokenWalletConstants.target_gas_balance, (address(this).balance - msg.value));
            require((address(this).balance > (reserve + TONTokenWalletConstants.target_gas_balance)), TONTokenWalletErrors.error_low_message_value);
            tvm.rawReserve(reserve, 2 );
            tvm.rawReserve(math.max(TONTokenWalletConstants.target_gas_balance, (address(this).balance - msg.value)), 2 );
        }
      else
        {
            require((msg.value > TONTokenWalletConstants.target_gas_balance), TONTokenWalletErrors.error_low_message_value);
            tvm.rawReserve((address(this).balance - msg.value), 2 );
        }
      balance_ -= tokens;
      allowance_.set(AllowanceInfo((allowance_.get().remaining_tokens - tokens), allowance_.get().spender));
      ITONTokenWallet(to).internalTransfer {value: 0 ,bounce: true,flag: 129 }(tokens, wallet_public_key, owner_address, send_gas_to, notify_receiver, payload);
  }
  function burnByOwner(uint128 tokens, uint128 grams, address send_gas_to, address callback_address, TvmCell callback_payload) external override onlyOwner() {
      require((tokens > 0 ));
      require((tokens <= balance_), TONTokenWalletErrors.error_not_enough_balance);
      require((((owner_address.value != 0 ) && (msg.value > 0 )) || (((owner_address.value == 0 ) && (grams <= address(this).balance)) && (grams > 0 ))), TONTokenWalletErrors.error_low_message_value);
      if ((owner_address.value != 0 ))
        {
            tvm.rawReserve(math.max(TONTokenWalletConstants.target_gas_balance, (address(this).balance - msg.value)), 2 );
            balance_ -= tokens;
            IBurnableTokenRootContract(root_address).tokensBurned {value: 0 ,flag: 128 ,bounce: true}(tokens, wallet_public_key, owner_address, ((send_gas_to.value != 0 ) ? send_gas_to : owner_address), callback_address, callback_payload);
        }
      else
        {
            tvm.accept();
            balance_ -= tokens;
            IBurnableTokenRootContract(root_address).tokensBurned {value: grams,bounce: true}(tokens, wallet_public_key, owner_address, ((send_gas_to.value != 0 ) ? send_gas_to : address(this)), callback_address, callback_payload);
        }
  }
  function burnByRoot(uint128 tokens, address send_gas_to, address callback_address, TvmCell callback_payload) external override onlyRoot() {
      require((tokens > 0 ));
      require((tokens <= balance_), TONTokenWalletErrors.error_not_enough_balance);
      tvm.rawReserve((address(this).balance - msg.value), 2 );
      balance_ -= tokens;
      IBurnableTokenRootContract(root_address).tokensBurned {value: 0 ,flag: 128 ,bounce: true}(tokens, wallet_public_key, owner_address, send_gas_to, callback_address, callback_payload);
  }
  function setReceiveCallback(address receive_callback_, bool allow_non_notifiable_) external override onlyOwner() {
      tvm.accept();
      receive_callback = receive_callback_;
      allow_non_notifiable = allow_non_notifiable_;
  }
  function setBouncedCallback(address bounced_callback_) external override onlyOwner() {
      tvm.accept();
      bounced_callback = bounced_callback_;
  }
  function destroy(address gas_dest) public override onlyOwner() {
      require((balance_ == 0 ));
      tvm.accept();
      selfdestruct(gas_dest);
  }
  modifier onlyRoot() {
      require((root_address == msg.sender), TONTokenWalletErrors.error_message_sender_is_not_my_root);
      _;
  }
  modifier onlyOwner() {
      require((((owner_address.value != 0 ) && (owner_address == msg.sender)) || ((wallet_public_key != 0 ) && (wallet_public_key == msg.pubkey()))), TONTokenWalletErrors.error_message_sender_is_not_my_owner);
      _;
  }
  modifier onlyInternalOwner() {
      require(((owner_address.value != 0 ) && (owner_address == msg.sender)));
      _;
  }
  function getExpectedAddress(uint256 wallet_public_key_, address owner_address_) private view inline returns (address) {
      TvmCell stateInit = tvm.buildStateInit({contr: TONTokenWallet,varInit:  {root_address: root_address,code: code,wallet_public_key: wallet_public_key_,owner_address: owner_address_},pubkey: wallet_public_key_,code: code});
      return  address(tvm.hash(stateInit));
  }
  onBounce(TvmSlice body) external {
      tvm.accept();
      uint32 functionId = body.decode(uint32);
      if ((functionId == tvm.functionId(ITONTokenWallet.internalTransfer)))
        {
            uint128 tokens = body.decode(uint128);
            balance_ += tokens;
            if ((bounced_callback.value != 0 ))
              {
                  tvm.rawReserve((address(this).balance - msg.value), 2 );
                  ITokensBouncedCallback(bounced_callback).tokensBouncedCallback {value: 0 ,flag: 128 }(address(this), root_address, tokens, msg.sender, balance_);
              }
            else
              if ((owner_address.value != 0 ))
                {
                    tvm.rawReserve(math.max(TONTokenWalletConstants.target_gas_balance, (address(this).balance - msg.value)), 2 );
                    owner_address.transfer({value: 0 ,flag: 128 });
                }
        }
      else
        if ((functionId == tvm.functionId(IBurnableTokenRootContract.tokensBurned)))
          {
              balance_ += body.decode(uint128);
              if ((owner_address.value != 0 ))
                {
                    tvm.rawReserve(math.max(TONTokenWalletConstants.target_gas_balance, (address(this).balance - msg.value)), 2 );
                    owner_address.transfer({value: 0 ,flag: 128 });
                }
          }
  }
  fallback() external {
  }
}


