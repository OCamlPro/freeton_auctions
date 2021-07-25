# On-line Auctions

This project contains smart contracts for on-line auctions on Free-TON.

## Overview

The following contracts are implemented in Solidity:

* `contracts/OCP_AutomaticDutchAuction.spp`: Direct Dutch auctions where the
    the price decreases automatically with time until `price_stop` is reached.

* `contracts/OCP_ManualDutchAuction.spp`: Direct Dutch auctions where
    the the price decreases from `price_start` to `price_stop` only
    when the auction house decides to decrease it step by step.

* `contracts/OCP_EnglishAuction.spp` : Standard Direct English auctions,
    with `bid_min_increment` (if not-zero, percent of how a bid must
     increase on the previous bid) and `time_delay` (if not-zero,
     if no bid comes after this delay, the current bid wins, even before
     `time_stop`).

* `contracts/OCP_ReverseEnglishAuction.spp` : Reverse variant of the
    English auctions. Bidders competes to sell their merchandise at the
    lowest price for the auctioner.

* `contracts/OCP_ReverseAutomaticDutchAuction.spp` : Reverse variant of the
    Dutch auctions with automatic increase of price over time. Bidders competes
    to sell their merchandise at the lowest price for the auctioner.

For all of these contracts, both TON Crystal tokens and TIP-3 tokens
are supported (we used Broxus contracts for interfaces).

For direct auctions, simple transfers are used (either in TON Crystal
to the auction contract, or in TIP-3 tokens to the auction TIP-3
wallet). The winner gets control over the auction contract, and can use
the `sendTransaction` method (same interface as multisig), to benefit from
what the auctioner sold (the auctioner is supposed to give control of the
sold resource to that auction contract before the auction).

For reverse auctions, the auctioner must transfer his tokens (TON or
TIP-3) to the auction wallet before the auction start. Then, bidders
must create `OCP_AuctionBidder` contracts (using the `new_bidder`
method of the auction) and transfer their merchandise (TIP-3) to the
bidder contract vault. Once the merchandise is present, the bidder
contract can issue bids using its 'bid' method. At the end of the
auction, the auctioner tokens are transferred to the winner, while the
winner's contract vault content is transferred to the auctionner's
vault.

## Directories

* `contracts/`: all the contracts that can actually be instanciated
* `abstract-contracts/`: all the abstract contracts, i.e. with no constructor
* `broxus-token-contracts/`: token contracts by Broxus for use as TIP-3 tokens
* `external-interfaces/`: the minimal interfaces used for external contracts
    (TIP-3 tokens)
* `interfaces/`: the minimal interfaces used between our contracts
* `libraries/`: the library files used by the project
