{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";
    flake-utils.url = "github:numtide/flake-utils";
    purescript-overlay = {
      url = "github:thomashoneyman/purescript-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, purescript-overlay }: 
    flake-utils.lib.eachDefaultSystem (system:
      let 
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            purescript-overlay.overlays.default
          ];
        }; 
      in 
        {
          devShells.default = pkgs.mkShellNoCC {
            buildInputs = with pkgs; [
              purs 
              spago-unstable
              purs-tidy-bin.purs-tidy-0_10_0
              purs-backend-es
              nodejs_24
              esbuild
            ]; 
          };
        }
    );
}
