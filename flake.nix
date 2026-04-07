{
  description = "nanoda_lib - A type checker for the Lean 4 programming language";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };
  outputs = { self, nixpkgs, rust-overlay }:
    let
      supportedSystems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = nixpkgs.lib.genAttrs supportedSystems;
    in {
      devShells = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; overlays = [ rust-overlay.overlays.default ]; };
          rustToolchain = pkgs.rust-bin.stable.latest.default.override { extensions = [ "rust-src" "rust-analyzer" ]; };
        in { default = pkgs.mkShell { buildInputs = [ rustToolchain pkgs.just pkgs.cargo-flamegraph pkgs.perf ]; }; });
      packages = forAllSystems (system:
        let pkgs = import nixpkgs { inherit system; overlays = [ rust-overlay.overlays.default ]; };
        in { default = pkgs.rustPlatform.buildRustPackage { pname = "nanoda_lib"; version = "0.4.6-beta"; src = ./.; cargoLock.lockFile = ./Cargo.lock; }; });
    };
}
