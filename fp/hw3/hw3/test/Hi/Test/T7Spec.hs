module Hi.Test.T7Spec (spec) where

import Text.RawString.QQ

import HW3.Action

import Hi.Test.Common
import System.Directory
import qualified System.IO.Strict as SIO
import System.IO.Unsafe (unsafePerformIO)

import qualified Data.Set as Set

spec :: Spec
spec = do
#if HI_TEST_UPTO < 7
  emptyTest
#else
  let testEvalIO = testEvalM . unwrapHIO . Set.fromList
  let testEvalIO' = testEvalIO [minBound..maxBound]
  -- | I failed to lift IO in test, it is avaliable in "it", but not here
  let !cwd0 = unsafePerformIO getCurrentDirectory
  after_ (setCurrentDirectory cwd0) $ describe "actions" do
    let
      dummyApplications =
        [ [r|cd("a")|]
        , [r|mkdir("dir")|]
        , [r|read("fle")|]
        , [r|write("to", [# 30 #])|]
        ]
    it "constants" do
      let check s = s ~=?? Ok s
      check "cd"
      check "cd"
      check "mkdir"
      check "read"
      check "write"
      mapM_ (\s -> s ~=?? Ok s) dummyApplications
      [r|write("to", "Hi!")|] ~=?? Ok [r|write("to", [# 48 69 21 #])|]
    it "run parses" do
      mapM_ (\s -> s ++ "!" ~=?? Ok "null") dummyApplications
    it "IO" do
      cwd <- getCurrentDirectory
      testEvalIO'
          [r|if(true, cwd, cwd)!|]
        `shouldBe` Ok (show cwd)
      testEvalIO'
          [r|read("test/exec/read.test")!|]
        `shouldBe` Ok [r|"303030\n"|]
      testEvalIO'
          [r|read("test/ls")!|]
        `shouldBe` Ok [r|[ "1" ]|]
      testEvalIO'
          [r|read("test/ls/2")!|]
        `shouldBe` Ok [r|null|]
      testEvalIO'
          [r|cd("test/exec")!|]
        `shouldBe` Ok [r|null|]
      testEvalIO'
          [r|write("write.test", encode-utf8("30"))!|]
        `shouldBe` Ok [r|null|]
      testEvalIO'
          [r|read("write.test")!|]
        `shouldBe` Ok [r|"30"|]
      testEvalIO'
          [r|write("write.test", encode-utf8("1000-7"))!|]
        `shouldBe` Ok [r|null|]
      -- bug with lazy IO
      v1000m7 <- SIO.readFile "write.test"
      v1000m7 `shouldBe` "1000-7"
      testEvalIO'
          [r|read("read.test")!|]
        `shouldBe` Ok [r|"303030\n"|]
    it "permissions" do
      let
        banned b act =
          testEvalIO
            (filter (/= b) [minBound..maxBound])
            act
          `shouldBe` Perm b
      banned AllowRead [r|read("read.test")!|]
      banned AllowRead [r|cwd!|]
      banned AllowWrite [r|write("write.test", [# 65 #])!|]
      banned AllowWrite [r|mkdir("testmk")!|]
      banned AllowRead [r|cd("..")!|] -- why read?!
    it "read-string" do
      testEvalIO
          [AllowWrite]
          [r|write("test/exec/write.test", [# ff #])!|]
        `shouldBe` Ok [r|null|]
      testEvalIO
          [AllowRead]
          [r|read("test/exec/write.test")!|]
        `shouldBe` Ok [r|[# ff #]|]
    it "lazy" do
      testEvalIO
          [AllowWrite]
          -- move bang out of if to additionally test propogation
          [r|if(false, write("test/exec/write.test", "nonlazy")!, write("test/exec/write.test", encode-utf8("lazy")))!|]
        `shouldBe` Ok [r|null|]
      lz <- SIO.readFile "test/exec/write.test"
      lz `shouldBe` "lazy"
      testEvalIO
          [AllowWrite]
          -- meve bang out of if to additionally test propogation
          [r|if(true, write("test/exec/write.test", encode-utf8("for sure"))!, write("test/exec/write.test", "oops leftmost")!)|]
        `shouldBe` Ok [r|null|]
      sure <- SIO.readFile "test/exec/write.test"
      sure `shouldBe` "for sure"
#endif
