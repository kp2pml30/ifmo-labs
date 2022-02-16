module Hi.Test.T11Spec (spec) where

import Text.RawString.QQ

import Hi.Test.Common

spec :: Spec
spec = do
  describe "better-ids" do
    it "-" do
      [r|echo.hello-world|] ~=?? Ok [r|echo("hello-world")|]
      [r|echo.hello-|] ~=?? ParseError "not sep-by"
      [r|echo.hello--world|] ~=?? ParseError "not sep-by"
      [r|reverse.hello|] ~=?? Ok [r|"olleh"|]
  describe "dictionaries" do
    it "dict literal" do
      [r|{ "width": 120, "height": 80 }|] ~=?? Ok [r|{ "height": 80, "width": 120 }|]
      [r|{}|] ~=?? Ok [r|{  }|]
      [r|  { "a"  : 0 }  |] ~=?? Ok [r|{ "a": 0 }|]
    it "dict literal 2" do
      [r|  { 1 + 2  : 20 + 10 }  |] ~=?? Ok [r|{ 3: 30 }|]
    it "dict func" do
      [r|{ "width": 120, "height": 80 }("width")|] ~=?? Ok "120"
    it "dict null" do
      [r|{ "width": 120, "height": 80 }("aaaa")|] ~=?? Ok "null"
    it "dict dot" do
      [r|{ "width": 120, "height": 80 }.width|] ~=?? Ok "120"
      [r|{ "complex-k-e1": 30 }.complex-k-e1|] ~=?? Ok "30"
      [r|{ "": 30 }.|] ~=?? ParseError "empty identifier"
      [r|{ "a": 30 }.b|] ~=?? Ok "null"
    it "keys and values" do
      [r|keys({ "width": 120, "height": 80 })|] ~=?? Ok [r|[ "height", "width" ]|]
      [r|values({ "width": 120, "height": 80 })|] ~=?? Ok [r|[ 80, 120 ]|]
    it "count" do
      [r|count("XXXOX")|] ~=?? Ok [r|{ "O": 1, "X": 4 }|]
      [r|count([# 58 58 58 4f 58 #])|] ~=?? Ok [r|{ 79: 1, 88: 4 }|]
      [r|count([true, true, false, true])|] ~=?? Ok [r|{ false: 1, true: 3 }|]
    it "invert" do
      [r|invert({ "x": 1, "y" : 2, "z": 1 })|] ~=?? Ok [r|{ 1: [ "z", "x" ], 2: [ "y" ] }|]
    it "int-index" do
      [r|count("Hello World").o|] ~=?? Ok "2"
      [r|invert(count("big blue bag"))|] ~=?? Ok [r|{ 1: [ "u", "l", "i", "e", "a" ], 2: [ "g", " " ], 3: [ "b" ] }|]
      [r|fold(add, values(count("Hello, World!")))|] ~=?? Ok "13"
    it "postfix operators" do
      [r|{ "a" : { "a" : cwd } }.a.a!|] ~=?? Ok "null"
      [r|{ "a" : { "b" : cwd } }.a.b!|] ~=?? Ok "null"
      [r|{ "a" : { "b" : add } }.a.b(10, 20)|] ~=?? Ok "30"
      [r|if(true, { "width" : 1 }, 1+1).width|] ~=?? Ok "1"
      [r|{ "add" : "str" }.add(0, 1)|] ~=?? Ok [r|"s"|]
    it "empty fold" do
      "fold(add, [])" ~=?? Ok "null"
    it "generalized-fold" do
      "fold(add, [# 01 ff #])" ~=?? Ok "256"
      [r|fold(add, "zadanie chto nado!")|] ~=?? Ok [r|"zadanie chto nado!"|]
      [r|fold(div, "")|] ~=?? Ok [r|null|]
      [r|fold(div, "beda")|] ~=?? Ok [r|"b/e/d/a"|]
      [r|fold(div, "3")|] ~=?? Ok [r|"3"|]
