{-# LANGUAGE TemplateHaskell #-}
module Main where

import Control.Monad.IO.Class (liftIO)
import Control.Monad (void)
import System.Exit (ExitCode(..))
import System.Directory (withCurrentDirectory)
import System.Process (readProcessWithExitCode)
import Lens.Micro
import Lens.Micro.TH
import qualified Graphics.Vty as V

import Brick
  ( hLimit, vLimit, hBox, vBox
  , Widget, str
  )
import qualified Brick as B
import qualified Brick.Main as M
import qualified Brick.Types as T
import qualified Brick.Widgets.Center as C
import qualified Brick.Widgets.Edit as E
import qualified Brick.AttrMap as A
import qualified Brick.Widgets.Border as Br
import qualified Brick.Widgets.Border.Style as BrS
import Brick.Util (on)

withBorder, withBorderSelected :: String -> Widget n -> Widget n
-- | Render a given widget inside a box with /unicode/ border.
withBorder           = withBorderStyle BrS.unicode
-- | Render a given widget inside a box with /unicode/ and /bold/ border.
withBorderSelected   = withBorderStyle BrS.unicodeBold

-- | Render given 'Widget' inside a box with the given title and border style.
withBorderStyle :: BrS.BorderStyle -> String -> B.Widget n -> Widget n
withBorderStyle style s w =
    B.withBorderStyle style
  $ Br.borderWithLabel (str s)
  $ B.padAll 1
  $ w

type Name = ()

data St = St
  { _edit   :: E.Editor String Name
  , _target :: String
  , _cabal  :: String
  }
makeLenses ''St

interpret :: String -> IO (String, String)
interpret s = withCurrentDirectory ".." $ do
  writeFile "REPL.agda" s
  (exitCode, cbl, _) <- readProcessWithExitCode "agda2hs" ["REPL.agda"] ""
  case exitCode of 
    ExitFailure n -> do
      return ("ERROR (" ++ show n ++ ")", cbl)
    ExitSuccess -> do
      s' <- readFile "REPL.hs"
      return (s', cbl)

drawUI :: St -> [T.Widget Name]
drawUI st = [ vBox
  [ B.vLimitPercent 70 $ hBox
    [ B.hLimitPercent 50 $
        withBorder "Source" $
          E.renderEditor (str . unlines) True (st^.edit)
    , B.hLimitPercent 50 $
        withBorder "Target" $
          str (st^.target)
    ]
  , B.vLimitPercent 30 $
      str (st^.cabal)
  ]]
  where withBorder = withBorderStyle BrS.unicode

appEvent :: St -> T.BrickEvent Name e -> T.EventM Name (T.Next St)
appEvent st (T.VtyEvent ev) =
  case ev of
    V.EvKey V.KEsc [] -> M.halt st
    V.EvKey V.KEnter [V.MMeta] -> do
      (trg, cbl) <- liftIO (interpret $ unlines $ E.getEditContents (st^.edit))
      M.continue $ st & target .~ trg
                      & cabal  .~ cbl
    _ -> M.continue =<< T.handleEventLensed st edit E.handleEditorEvent ev
appEvent st _ = M.continue st

initialState :: St
initialState = St (E.editor () Nothing "") "     " "      "
       
theMap :: A.AttrMap
theMap = A.attrMap V.defAttr
    [ (E.editAttr,        V.white `on` V.blue)
    , (E.editFocusedAttr, V.black `on` V.yellow)
    ]

theApp :: M.App St e Name
theApp =
    M.App { M.appDraw = drawUI
          , M.appChooseCursor = M.showFirstCursor
          , M.appHandleEvent = appEvent
          , M.appStartEvent = return
          , M.appAttrMap = const theMap
          }

main :: IO ()
main = void $ M.defaultMain theApp initialState
