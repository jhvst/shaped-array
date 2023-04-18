{
  inputs = { };
  outputs =
    { self
    , nixpkgs
    , flake-utils
    , ...
    }:
    flake-utils.lib.eachDefaultSystem (system:
    let
      overlays = [ ];
      pkgs = import nixpkgs { inherit system overlays; };
    in
    {
      devShells.default = pkgs.mkShell {
        buildInputs = [
        ];
        packages = with pkgs; [
          idris
        ];
      };
      packages.default = pkgs.idrisPackages.build-idris-package {
        pname = "shaped-array";
        version = "unstable";

        ipkgName = "Shaped";

        src = ./.;

        meta.homepage = "https://github.com/jhvst/shaped-array";
      };
    });
}
