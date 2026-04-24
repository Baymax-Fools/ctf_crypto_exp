from PIL import Image, ImageSequence
import os
from pyzbar.pyzbar import decode
import cv2


def save_gif_frames_as_png(gif_path, output_folder="output"):
    #  将GIF的每一帧保存为PNG图片。
    #  参数:
    #  gif_path (str): GIF文件的路径。
    # output_folder (str): 保存PNG图片的文件夹。默认为"output"。

    # 确保输出文件夹存在
    if not os.path.exists(output_folder):
        os.makedirs(output_folder)

        # 打开GIF文件
    with Image.open(gif_path) as img:
        # 遍历GIF的每一帧
        frames = [frame.copy() for frame in ImageSequence.Iterator(img)]

        # 为每一帧保存一个PNG文件
        for index, frame in enumerate(frames):
            frame.save(os.path.join(output_folder, f"frame_{index:03d}.png"))
        # 使用示例


gif_path = "CTF.gif"  # 替换为你的GIF文件路径
save_gif_frames_as_png(gif_path)


def scan_qr_code(image_path):
    # 读取图片
    image = cv2.imread(image_path)
    # 解码图片中的二维码
    decoded_objects = decode(image)
    for obj in decoded_objects:
        print("Type:", obj.type)
        print("Data:", obj.data.decode("utf-8"))


if __name__ == "__main__":
    for i in range(1, 700):
        i = str(i)
        if len(i) == 1:
            i = "00" + i
        elif len(i) == 2:
            i = "0" + i
        image_path = 'output/frame_' + i + '.png'
        scan_qr_code(image_path)