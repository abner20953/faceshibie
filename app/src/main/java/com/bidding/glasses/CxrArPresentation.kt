package com.bidding.glasses

import android.app.Presentation
import android.content.Context
import android.os.Bundle
import android.view.Display
import android.view.WindowManager
import androidx.core.content.ContextCompat
import com.bidding.glasses.databinding.ViewGlassArOverlayBinding
import java.util.Locale

/**
 * 基于 Android 标准 Presentation 架构的多屏渲染实现。
 * 在 Rokid 智能眼镜系统中，用于在眼镜的投影辅助屏上进行多专家核验卡片渲染，支持空间姿态防抖。
 */
class CxrArPresentation(outerContext: Context, display: Display) : Presentation(outerContext, display) {

    private lateinit var binding: ViewGlassArOverlayBinding

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        
        binding = ViewGlassArOverlayBinding.inflate(layoutInflater)
        setContentView(binding.root)
        
        window?.let { win ->
            win.setType(WindowManager.LayoutParams.TYPE_PRIVATE_PRESENTATION)
            win.addFlags(WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE)
            win.addFlags(WindowManager.LayoutParams.FLAG_NOT_TOUCHABLE)
            win.setDimAmount(0f)
        }
    }

    /**
     * 动态设置专家核验卡片信息，支持多专家时显示当前索引及总人数
     * @param currentIndex 当前专家的序号（0-indexed）
     * @param totalCount 本帧匹配到的总专家人数
     */
    fun showExpertInfo(
        name: String, 
        company: String, 
        major: String, 
        phone: String, 
        score: Float, 
        currentIndex: Int, 
        totalCount: Int,
        liveFace: android.graphics.Bitmap?,
        systemFace: android.graphics.Bitmap?
    ) {
        if (!::binding.isInitialized) {
            return
        }
        
        binding.tvArScore.text = String.format(Locale.getDefault(), "%.1f%%", score)
        binding.tvArName.text = name
        binding.tvArCompany.text = company
        binding.tvArMajor.text = major
        binding.tvArPhone.text = phone

        // 设置比对照片
        binding.ivCropFace.setImageBitmap(liveFace)
        binding.ivSystemFace.setImageBitmap(systemFace)

        // 如果识别到多名专家，在标题栏显示页码（如：👤 候选专家 1/3）
        if (totalCount > 1) {
            binding.tvArHeader.text = String.format(Locale.getDefault(), "👤 候选专家 %d/%d", currentIndex + 1, totalCount)
            binding.tvArHeader.setTextColor(ContextCompat.getColor(context, R.color.accent_warning_orange))
            binding.tvArScore.setTextColor(ContextCompat.getColor(context, R.color.accent_warning_orange))
        } else {
            binding.tvArHeader.text = "👤 评标专家比对通过"
            binding.tvArHeader.setTextColor(ContextCompat.getColor(context, R.color.accent_aurora_green))
            binding.tvArScore.setTextColor(ContextCompat.getColor(context, R.color.accent_aurora_green))
        }
    }

    fun setLiveFace(bitmap: android.graphics.Bitmap?) {
        if (::binding.isInitialized) {
            binding.ivCropFace.setImageBitmap(bitmap)
        }
    }

    fun setSystemFace(bitmap: android.graphics.Bitmap?) {
        if (::binding.isInitialized) {
            binding.ivSystemFace.setImageBitmap(bitmap)
        }
    }
}
