{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -Wno-missing-fields #-}

import Foreign
import Foreign.C.String hiding (CString)
import Foreign.C.Types
import Foreign.Marshal.Alloc
import Foreign.Ptr
import Foreign.Storable
import Data.Set as S
import Test.QuickCheck hiding (Success)
import Test.QuickCheck.Gen
import Test.QuickCheck.Monadic

import CogentMonad
import FFI (Ct432(..), Ct435(..), pDummyCSysState, dummyCSysState, const_unit, const_true, const_false)
import qualified FFI as FFI
import Fsop_Shallow_Desugar 
-- import WordArray


hs_fsm_init :: MountState -> FsmState -> Cogent_monad (Either ErrCode FsmState)
hs_fsm_init mount_st fsm_st = do
  nb_free_eb <- return $ nb_eb (super mount_st) - bilbyFsFirstLogEbNum
  (return $ Left eNoMem) `alternative` (return $ Right $ fsm_st { nb_free_eb })


r_result :: Either ErrCode FsmState -> Cogent_monad (Either ErrCode FsmState) -> Bool
r_result r1 r2 = r1 `member` r2

gen_MountState :: Gen MountState
gen_MountState = undefined

gen_FsmState :: Gen FsmState
gen_FsmState = undefined

prop_fsm_init_refine = monadicIO $ forAllM (gen_MountState) $ \mount_st ->
                                   forAllM (gen_FsmState) $ \fsm_st -> run $ do
                                     ra <- cogent_fsm_init mount_st fsm_st
                                     rc <- return $ hs_fsm_init mount_st fsm_st
                                     return $ ra `r_result` rc

foreign import ccall unsafe "wrapper_pp_inferred.c fsm_init"
  c_fsm_init :: Ptr Ct432 -> IO (Ptr Ct435)


conv_ObjSuper :: ObjSuper -> IO FFI.Ct39
conv_ObjSuper (R93 {..}) = 
  return $ FFI.Ct39 { FFI.nb_eb           = fromIntegral nb_eb
                    , FFI.eb_size         = fromIntegral eb_size
                    , FFI.io_size         = fromIntegral io_size
                    , FFI.nb_reserved_gc  = fromIntegral nb_reserved_gc
                    , FFI.nb_reserved_del = fromIntegral nb_reserved_del
                    , FFI.cur_eb          = fromIntegral cur_eb
                    , FFI.cur_offs        = fromIntegral cur_offs
                    , FFI.last_inum       = fromIntegral last_inum
                    , FFI.next_sqnum      = fromIntegral next_sqnum
                    }

conv_ObjData :: ObjData -> IO FFI.Ct62
conv_ObjData (R82 {..}) = do
  p_odata <- new =<< conv_WordArray_u8 odata
  return $ FFI.Ct62 (fromIntegral id) p_odata

conv_ObjDel :: ObjDel -> IO FFI.Ct63
conv_ObjDel (R79 x) = return $ FFI.Ct63 $ fromIntegral x

conv_Array_ObjDentry :: Array ObjDentry -> IO FFI.CArray_t48
conv_Array_ObjDentry = undefined

conv_ObjDentarr :: ObjDentarr -> IO FFI.Ct64
conv_ObjDentarr (R80 {..}) = do
  p_entries <- new =<< conv_Array_ObjDentry entries
  return $ FFI.Ct64 { id = fromIntegral id
                    , nb_dentry = fromIntegral nb_dentry
                    , entries = p_entries
                    }

conv_ObjInode :: ObjInode -> IO FFI.Ct45
conv_ObjInode (R83 {..}) = 
  return $ FFI.Ct45 { FFI.id        = fromIntegral id
                    , FFI.size      = fromIntegral size
                    , FFI.atime_sec = fromIntegral atime_sec
                    , FFI.ctime_sec = fromIntegral ctime_sec
                    , FFI.mtime_sec = fromIntegral mtime_sec
                    , FFI.nlink     = fromIntegral nlink
                    , FFI.uid       = fromIntegral uid
                    , FFI.gid       = fromIntegral gid
                    , FFI.mode      = fromIntegral mode
                    , FFI.flags     = fromIntegral flags
                    }

conv_WordArray_ObjSumEntry :: WordArray ObjSumEntry -> IO FFI.CWordArray_ut10
conv_WordArray_ObjSumEntry = undefined

conv_ObjSummary :: ObjSummary -> IO FFI.Ct42
conv_ObjSummary (R95 {..}) = do
  p_entries <- new =<< conv_WordArray_ObjSumEntry entries
  return $ FFI.Ct42 { FFI.nb_sum_entry = fromIntegral nb_sum_entry
                    , FFI.entries      = p_entries  -- :: Ptr FFI.CWordArray_ut10,
                    , FFI.sum_offs     = fromIntegral sum_offs
                    }

conv_ObjUnion :: ObjUnion -> IO FFI.Ct65
conv_ObjUnion ounion =
  case ounion of
    TObjData    t -> conv_ObjData    t         >>= \x -> return $ FFI.Ct65 { FFI.tag = FFI.Ctag_t $ fromIntegral $ fromEnum FFI.tag_ENUM_TObjData   , tObjData    = x }
    TObjDel     t -> conv_ObjDel     t         >>= \x -> return $ FFI.Ct65 { FFI.tag = FFI.Ctag_t $ fromIntegral $ fromEnum FFI.tag_ENUM_TObjDel    , tObjDel     = x }
    TObjDentarr t -> conv_ObjDentarr t >>= new >>= \x -> return $ FFI.Ct65 { FFI.tag = FFI.Ctag_t $ fromIntegral $ fromEnum FFI.tag_ENUM_TObjDentarr, tObjDentarr = x }
    TObjInode   t -> conv_ObjInode   t >>= new >>= \x -> return $ FFI.Ct65 { FFI.tag = FFI.Ctag_t $ fromIntegral $ fromEnum FFI.tag_ENUM_TObjInode  , tObjInode   = x }
    TObjPad     t ->                                     return $ FFI.Ct65 { FFI.tag = FFI.Ctag_t $ fromIntegral $ fromEnum FFI.tag_ENUM_TObjPad    , tObjPad     = const_unit }
    TObjSummary t -> conv_ObjSummary t >>= new >>= \x -> return $ FFI.Ct65 { FFI.tag = FFI.Ctag_t $ fromIntegral $ fromEnum FFI.tag_ENUM_TObjSummary, tObjSummary = x }
    TObjSuper   t -> conv_ObjSuper   t >>= new >>= \x -> return $ FFI.Ct65 { FFI.tag = FFI.Ctag_t $ fromIntegral $ fromEnum FFI.tag_ENUM_TObjSuper  , tObjSuper   = x }

conv_Obj :: Obj -> IO FFI.Ct66
conv_Obj (R90 {..}) = do
  ounion' <- conv_ObjUnion ounion
  return $ FFI.Ct66 { FFI.magic  = fromIntegral magic
                    , FFI.crc    = fromIntegral crc
                    , FFI.sqnum  = fromIntegral sqnum
                    , FFI.offs   = fromIntegral offs
                    , FFI.trans  = fromIntegral trans
                    , FFI.otype  = fromIntegral otype
                    , FFI.ounion = ounion'
                    }

conv_UbiVolInfo :: UbiVolInfo -> IO FFI.CUbiVolInfo
conv_UbiVolInfo = return

conv_UbiDevInfo :: UbiDevInfo -> IO FFI.CUbiDevInfo
conv_UbiDevInfo = return

conv_MountState :: MountState -> IO FFI.Ct72
conv_MountState (R19 {..}) = do
  p_super   <- new =<< conv_ObjSuper super
  p_obj_sup <- new =<< conv_Obj obj_sup
  p_vol     <- new =<< conv_UbiVolInfo vol
  p_dev     <- new =<< conv_UbiDevInfo dev
  return $ FFI.Ct72 { eb_recovery      = fromIntegral eb_recovery
                    , eb_recovery_offs = fromIntegral eb_recovery_offs
                    , super            = p_super
                    , obj_sup          = p_obj_sup
                    , super_offs       = fromIntegral super_offs
                    , vol              = p_vol
                    , dev              = p_dev
                    , no_summary       = FFI.Cbool_t $ CUChar $ fromIntegral $ fromEnum no_summary
                    }

conv_WordArray_u8 :: WordArray Word8 -> IO FFI.CWordArray_u8
conv_WordArray_u8 = undefined

conv_WordArray_u32 :: WordArray Word32 -> IO FFI.CWordArray_u32
conv_WordArray_u32 = undefined

conv_Rbt_ObjId_GimNode :: Rbt ObjId GimNode -> IO FFI.CRbt_u64_ut18
conv_Rbt_ObjId_GimNode = undefined

conv_FsmState :: FsmState -> IO FFI.Ct68
conv_FsmState (R94 {..}) = do
  p_used_eb     <- new =<< conv_WordArray_u8 used_eb
  p_dirty_space <- new =<< conv_WordArray_u32 dirty_space
  p_gim         <- new =<< conv_Rbt_ObjId_GimNode gim
  return $ FFI.Ct68 { nb_free_eb  = fromIntegral nb_free_eb
                    , used_eb     = p_used_eb
                    , dirty_space = p_dirty_space
                    , gim         = p_gim
                    }

mk_fsm_init_arg :: MountState -> FsmState -> IO Ct432
mk_fsm_init_arg mount_st fsm_st = do
  p_sys_st   <- pDummyCSysState
  p_mount_st <- new =<< conv_MountState mount_st
  p_fsm_st   <- new =<< conv_FsmState fsm_st
  return $ Ct432 { p1 = p_sys_st, p2 = p_mount_st, p3 = p_fsm_st }

conv_Ct433 :: FFI.Ct433 -> IO ErrCode
conv_Ct433 (FFI.Ct433 {..}) = return $ fromIntegral p1

conv_CWordArray_u8 :: FFI.CWordArray_u8 -> IO (WordArray Word8)
conv_CWordArray_u8 = undefined

conv_CWordArray_u32 :: FFI.CWordArray_u32 -> IO (WordArray Word32)
conv_CWordArray_u32 = undefined

conv_CRbt_u64_ut18 :: FFI.CRbt_u64_ut18 -> IO (Rbt ObjId GimNode)
conv_CRbt_u64_ut18 = undefined

conv_Ct68 :: FFI.Ct68 -> IO FsmState
conv_Ct68 (FFI.Ct68 {..}) = do
  p_used_eb     <- peek used_eb     >>= conv_CWordArray_u8
  p_dirty_space <- peek dirty_space >>= conv_CWordArray_u32
  p_gim         <- peek gim         >>= conv_CRbt_u64_ut18
  return $ R94 (fromIntegral nb_free_eb) p_used_eb p_dirty_space p_gim

conv_Ct434 :: FFI.Ct434 -> IO (Either ErrCode FsmState)
conv_Ct434 (FFI.Ct434 {..}) = do
  let FFI.Ctag_t t = tag
  if | fromIntegral t == fromEnum FFI.tag_ENUM_Success -> conv_Ct433 error >>= return . Left
     | fromIntegral t == fromEnum FFI.tag_ENUM_Error   -> (conv_Ct68 =<< peek success) >>= return . Right

conv_Ct435 :: Ct435 -> IO (Either ErrCode FsmState)
conv_Ct435 (Ct435 {..}) = conv_Ct434 p2

mk_fsm_init_ret :: Ct435 -> IO (Either ErrCode FsmState)
mk_fsm_init_ret = conv_Ct435

cogent_fsm_init :: MountState -> FsmState -> IO (Either ErrCode FsmState)
cogent_fsm_init mount_st fsm_st = do
  p_arg <- new =<< mk_fsm_init_arg mount_st fsm_st
  p_ret <- c_fsm_init p_arg
  ret <- peek p_ret
  mk_fsm_init_ret ret
